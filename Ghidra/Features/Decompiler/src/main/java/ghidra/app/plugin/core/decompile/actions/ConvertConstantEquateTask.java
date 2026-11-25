/* ###
 * IP: GHIDRA
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */
package ghidra.app.plugin.core.decompile.actions;

import java.util.Arrays;
import java.util.LinkedHashSet;

import ghidra.app.decompiler.ClangToken;
import ghidra.app.decompiler.ClangVariableToken;
import ghidra.app.plugin.core.decompile.DecompilerActionContext;
import ghidra.app.plugin.core.decompile.actions.ConvertConstantAction.NearMatchValues;
import ghidra.program.database.symbol.EquateManager;
import ghidra.program.model.address.Address;
import ghidra.program.model.block.CodeBlock;
import ghidra.program.model.block.SimpleBlockModel;
import ghidra.program.model.data.*;
import ghidra.program.model.data.Enum;
import ghidra.program.model.listing.Instruction;
import ghidra.program.model.listing.Program;
import ghidra.program.model.pcode.*;
import ghidra.program.model.scalar.Scalar;
import ghidra.program.model.symbol.*;
import ghidra.util.Msg;
import ghidra.util.exception.*;
import ghidra.util.task.TaskMonitor;
import utility.function.Callback;

/**
 * Create an equate in the table for the specific Address and hash value.
 * The equate is not assumed to be attached to a particular instruction operand and
 * uses the dynamic hash value to identify the particular constant (within p-code) to label.
 *
 * If altAddress is non-null and the other alt* fields are filled in, the task attempts
 * to set the equation on the altAddress first to get the representation of the p-code
 * constant at convertAddress to change.  After the decompilation finishes, the representation
 * is checked, and if it did not change, the alt* equate is removed and an equate is created
 * directly for the convertAddress;
 */
public class ConvertConstantEquateTask implements Callback {
	/**
	 * Max instructions to search through, when looking for a scalar match in the listing
	 * that corresponds with the selected constant in the decompiler window.
	 */
	private final static int MAX_INSTRUCTION_WINDOW = 20;

	private static final int MAX_SCALAR_SIZE = 8;
	private record ExistingReference(Equate equate, EquateReference reference) {}
	private record EnumMember(Enum type, long value) {}

	private final DecompilerActionContext context;
	private final Program program;
	private ExistingReference previous;
	private EnumMember enumMember;
	private final Scalar convertValue;		// Constant being converted
	private Address convertAddress;		// The primary address of the Equate
	private String convertName;			// The primary name to use in the Equate table
	private long convertHash;			// A dynamic hash locating the constant Varnode in data-flow
	private int convertIndex;			// The scalar index associated with the primary Equate (or -1)

	private Address altAddress = null;	// Alternate location of constant
	private int altIndex;				// Index of alternate scalar
	private String altName = null;		// Alternate equate name
	private long altValue;				// Alternate value 

	/**
	 * A helper class describing a (matching) scalar operand
	 */
	private static class ScalarMatch {
		Address refAddr;		// Address of instruction
		Scalar scalar;
		int opIndex;

		public ScalarMatch(Address addr, Scalar value, int index) {
			refAddr = addr;
			scalar = value;
			opIndex = index;
		}
	}

	/**
	 * Construct a primary Equate task
	 * @param context is the action context for the task
	 * @param name is the primary Equate name
	 * @param addr is the primary address of the Equate
	 * @param scalar is the equate constant
	 * @param hash is the dynamic hash
	 * @param index is the operand index if the Equate is known to label an instruction operand
	 */
	public ConvertConstantEquateTask(DecompilerActionContext context, String name, Address addr,
			Scalar scalar, long hash, int index) {
		this.context = context;
		program = context.getProgram();
		convertValue = scalar;
		convertName = name;
		convertAddress = addr;
		convertHash = hash;
		convertIndex = index;
	}

	/**
	 * If the mouse context is on a constant that it suitable for a conversion using this task,
	 * return a description of the constant.  Otherwise return null.
	 * @param context is the mouse context
	 * @param convertType is the type of conversion being selected (FORMAT_DEC FORMAT_HEX etc.)
	 * @return the constant description or null
	 */
	static protected Scalar getConvertibleConstant(DecompilerActionContext context,
			int convertType) {
		ClangToken tokenAtCursor = context.getTokenAtCursor();
		if (!(tokenAtCursor instanceof ClangVariableToken)) {
			return null;
		}
		Varnode convertVn = tokenAtCursor.getVarnode();
		if (convertVn == null || !convertVn.isConstant() || convertVn.getSize() > MAX_SCALAR_SIZE) {
			return null;
		}

		HighSymbol symbol = convertVn.getHigh().getSymbol();
		EquateSymbol convertSymbol = null;
		if (symbol != null) {
			if (symbol instanceof EquateSymbol) {
				convertSymbol = (EquateSymbol) symbol;
				int type = convertSymbol.getConvert();
				if (type == convertType || type == EquateSymbol.FORMAT_DEFAULT) {
					return null;
				}
			}
			else {
				return null;		// Something already attached to constant
			}
		}

		DataType convertDataType = convertVn.getHigh().getDataType();
		boolean convertIsSigned = false;
		if (convertDataType instanceof AbstractIntegerDataType) {
			if (convertDataType instanceof BooleanDataType) {
				return null;
			}
			convertIsSigned = ((AbstractIntegerDataType) convertDataType).isSigned();
		}
		else if (convertDataType instanceof Enum) {
			return null;
		}
		return new Scalar(convertVn.getSize() * 8, convertVn.getOffset(), convertIsSigned);
	}

	/**
	 * Establish an alternate Equate to try before falling back on the primary Equate
	 * @param name is the alternate name of the Equate
	 * @param addr is the alternate address
	 * @param index is the operand index
	 * @param value is the alternate constant value to equate
	 */
	public void setAlternate(String name, Address addr, int index, long value) {
		altName = name;
		altAddress = addr;
		altValue = value;
		altIndex = index;
	}

	/**
	 * Remove the existing primary reference and check for conflicting references.
	 */
	private void removePrimaryReference() throws InvalidInputException {
		long targetHash = convertHash;
		if (previous != null) {
			if (!removeReference(program, previous.equate(), previous.reference())) {
				throw new InvalidInputException("Ambiguous equate reference");
			}
			if (targetHash == 0) {
				// Adding a Listing reference stores a hash if the instruction yields exactly one.
				Instruction instr = program.getListing().getInstructionAt(convertAddress);
				if (instr != null) {
					long value = enumMember == null ? convertValue.getValue() : enumMember.value();
					long[] hashes = DynamicHash.calcConstantHash(instr, value);
					targetHash = hashes.length == 1 ? hashes[0] : 0;
				}
			}
		}
		EquateTable equateTable = program.getEquateTable();
		for (Equate equate : equateTable.getEquates(convertAddress)) {
			for (EquateReference ref : equate.getReferences(convertAddress)) {
				if (ref.getDynamicHashValue() == targetHash &&
					(targetHash != 0 || ref.getOpIndex() == convertIndex)) {
					if (previous != null) {
						throw new InvalidInputException("Another equate already uses this reference");
					}
					if (!removeReference(program, equate, ref)) {
						throw new InvalidInputException("Ambiguous equate reference");
					}
					return;
				}
			}
		}
	}

	private static boolean removeReference(Program program, Equate equate, EquateReference ref) {
		if (equate.getReferenceCount() <= 1) {
			program.getEquateTable().removeEquate(equate.getName());
			return true;
		}
		long hash = ref.getDynamicHashValue();
		if (hash != 0) {
			equate.removeReference(hash, ref.getAddress());
		}
		else {
			long count = equate.getReferences(ref.getAddress()).stream()
					.filter(candidate -> candidate.getOpIndex() == ref.getOpIndex())
					.count();
			if (count != 1) {
				return false;
			}
			equate.removeReference(ref.getAddress(), ref.getOpIndex());
		}
		return true;
	}

	/**
	 * Remove the alternate reference installed by this task.
	 * @return true if the reference was found and removed
	 */
	private boolean removeAlternateReference() {
		Equate equate = program.getEquateTable().getEquate(altName);
		if (equate != null) {
			for (EquateReference ref : equate.getReferences(altAddress)) {
				if (ref.getOpIndex() == altIndex) {
					return removeReference(program, equate, ref);
				}
			}
		}
		return false;
	}

	/**
	 * Add the primary equate reference for the selected constant.
	 * @throws DuplicateNameException if there is already an equate with same name but different value
	 * @throws InvalidInputException if the equate cannot be created
	 */
	private void addPrimaryEquate() throws DuplicateNameException, InvalidInputException {
		Equate equate = getOrCreateEquate(convertName, convertValue.getValue());
		// Add reference to existing equate
		if (convertHash != 0) {
			equate.addReference(convertHash, convertAddress);
		}
		else {
			equate.addReference(convertAddress, convertIndex);
		}
	}

	/**
	 * Add the alternate equate reference at the matching instruction operand.
	 * @throws DuplicateNameException if there is already an equate with same name but different value
	 * @throws InvalidInputException if the equate cannot be created
	 */
	private void addAlternateEquate() throws InvalidInputException, DuplicateNameException {
		Equate equate = getOrCreateEquate(altName, altValue);
		equate.addReference(altAddress, altIndex);
		altName = equate.getName();
	}

	private Equate getOrCreateEquate(String name, long value)
			throws InvalidInputException, DuplicateNameException {
		if (enumMember != null) {
			DataTypeManager manager = program.getDataTypeManager();
			Enum chosen = enumMember.type();
			DataType resolved = manager.findDataTypeForID(chosen.getUniversalID());
			if (resolved == null) {
				resolved = manager.resolve(chosen, null);
			}
			if (!(resolved instanceof Enum enoom) || !enoom.contains(enumMember.value())) {
				throw new InvalidInputException("The program enum has no matching member");
			}
			value = enumMember.value();
			name = EquateManager.formatNameForEquate(enoom.getUniversalID(), value);
		}
		EquateTable equateTable = program.getEquateTable();
		Equate equate = equateTable.getEquate(name);

		if (equate != null && equate.getValue() != value) {
			String msg = "Equate named " + name + " already exists with value of " +
				equate.getValue() + ".";
			throw new DuplicateNameException(msg);
		}

		if (equate == null) {
			equate = equateTable.createEquate(name, value);
		}

		return equate;
	}

	/**
	 * Create a reference to primary equate, removing any previous reference.
	 * If an alternate equate is given, remove any existing reference to it as well.
	 */
	private void applyPrimaryEquate() {

		int transaction = program.startTransaction("Convert constant");
		boolean commit = false;
		try {
			if (altAddress != null && !removeAlternateReference()) {
				return;
			}
			removePrimaryReference();
			addPrimaryEquate();
			commit = true;
		}
		catch (DuplicateNameException e) {
			Msg.showError(this, null, "Convert Failed", e.getMessage());
		}
		catch (InvalidInputException e) {
			Msg.showError(this, null, "Convert Failed", e.getMessage());
		}
		finally {
			program.endTransaction(transaction, commit);
		}
	}

	/**
	 * Create a reference to the alternate equate.
	 */
	private boolean applyAlternateEquate() {
		int transaction = program.startTransaction("Convert constant");
		boolean commit = false;
		try {
			EquateTable table = program.getEquateTable();
			boolean occupied = enumMember != null ? !table.getEquates(altAddress).isEmpty()
					: !table.getEquates(altAddress, altIndex).isEmpty();
			if (occupied) {
				altAddress = null;
			}
			else {
				addAlternateEquate();
			}
			commit = true;
		}
		catch (DuplicateNameException e) {
			Msg.showError(this, null, "Convert Failed", e.getMessage());
		}
		catch (InvalidInputException e) {
			Msg.showError(this, null, "Convert Failed", e.getMessage());
		}
		finally {
			program.endTransaction(transaction, commit);
		}
		return commit;
	}

	/**
	 * Look for the EquateSymbol pointing to the altAddress, attached to the constant
	 * @return true if we find the EquateSymbol, false otherwise
	 */
	private boolean isAlternatePlaced() {
		HighFunction highFunction = context.getHighFunction();	// Get the updated HighFunction
		if (highFunction == null) {
			return false;
		}
		// Varnode itself should be unchanged
		Varnode vn = DynamicHash.findVarnode(highFunction, convertAddress, convertHash);
		if (vn == null) {
			return false;
		}
		HighSymbol symbol = vn.getHigh().getSymbol();	// But now it should have an equate on it
		if (!(symbol instanceof EquateSymbol eqSymbol) || !altAddress.equals(eqSymbol.getPCAddress())) {
			return false;
		}
		if (enumMember == null) {
			return true;
		}
		Equate alternate = program.getEquateTable().getEquate(altName);
		return alternate != null && eqSymbol.getValue() == enumMember.value() &&
			alternate.getDisplayName().equals(eqSymbol.getName());
	}

	/**
	 * Callback executed after the alternative equate is placed and the DecompilerProvider has updated its window.
	 * We check to see if the equate reached the desired constant in the decompiler.
	 * If not, we remove the alternate equate and place a direct equate
	 */
	@Override
	public void call() {
		if (isAlternatePlaced()) {
			return;
		}
		applyPrimaryEquate();
	}

	/**
	 * Run the convert task.  If the task is given an alternate equate, this is placed, otherwise
	 * the primary equate is placed.  If an alternate is placed, a thread is scheduled to check if
	 * the alternate equate reached the constant Varnode.  If not the alternate equate reference is
	 * removed, and the task falls back and places the primary equate.
	 */
	public void runTask() {
		if (altAddress != null && !applyAlternateEquate()) {
			return;
		}
		if (altAddress != null) {
			try {
				Thread.sleep(50);		// Let the decompiler get going
			}
			catch (InterruptedException e) {
				return;
			}
			context.getComponentProvider().doWhenNotBusy(this);
		}
		else {
			applyPrimaryEquate();
		}
	}

	/**
	 * Find an operand matching the enum member or one of the nearby scalar values.
	 * @param instr is the instruction
	 * @param values is the set of nearby values to match
	 * @param member is the enum member to match, or null to use nearby values
	 * @return the match, with operand index -1 for multiple matches, or null for no match
	 */
	private static ScalarMatch findScalarInInstruction(Instruction instr, NearMatchValues values,
			EnumMember member) {
		int numOperands = instr.getNumOperands();
		ScalarMatch scalarMatch = null;
		for (int i = 0; i < numOperands; i++) {
			for (Object obj : instr.getOpObjects(i)) {
				if (obj instanceof Scalar) {
					Scalar scalar = (Scalar) obj;
					boolean matches = member == null ? values.isMatch(scalar.getValue())
							: scalar.getValue() == member.value() || scalar.getSignedValue() == member.value();
					if (matches) {
						if (scalarMatch != null) {
							scalarMatch.opIndex = -1;	// non-unique scalar operand value - can't identify operand
							return scalarMatch;
						}
						scalarMatch = new ScalarMatch(instr.getAddress(), scalar, i);
					}
				}
			}
		}
		return scalarMatch;
	}

	/**
	 * Search backward within the basic block for a unique matching scalar.
	 * Enum members require a matching value. Other equates can match nearby values.
	 * @param program is the Program
	 * @param startAddress is the starting address to search backward from
	 * @param scalar is the constant value to search for
	 * @param member is the selected enum member, or null for another kind of equate
	 * @return a description of the scalar match, or null if there is no match
	 */
	private static ScalarMatch findScalarMatch(Program program, Address startAddress,
			Scalar scalar, EnumMember member) {
		NearMatchValues values = member == null ? new NearMatchValues(scalar) : null;
		int count = 0;
		ScalarMatch match = null;
		Instruction curInst = program.getListing().getInstructionAt(startAddress);
		if (curInst == null) {
			return null;
		}

		SimpleBlockModel model = new SimpleBlockModel(program);
		CodeBlock basicBlock = null;
		try {
			basicBlock = model.getFirstCodeBlockContaining(startAddress, TaskMonitor.DUMMY);
		}
		catch (CancelledException e) {
			// can't happen; dummy monitor
		}
		if (basicBlock == null) {
			return null;
		}

		while (count < MAX_INSTRUCTION_WINDOW) {
			count += 1;
			ScalarMatch newMatch = findScalarInInstruction(curInst, values, member);
			if (newMatch != null) {
				if (match != null) {
					return null;		// Matches at more than one address
				}
				if (newMatch.opIndex < 0) {
					return null;		// Matches at more than one operand
				}
				match = newMatch;
			}
			curInst = curInst.getPrevious();
			if (curInst == null) {
				break;
			}
			if (!basicBlock.contains(curInst.getAddress())) {
				break;
			}
		}
		if (match != null && member == null) {
			if (match.scalar.bitLength() < 8 || match.scalar.isSigned() != scalar.isSigned()) {
				int size = match.scalar.bitLength();
				if (size < 8)
					size = 8;
				match.scalar = new Scalar(size, match.scalar.getUnsignedValue(), scalar.isSigned());
			}
		}
		return match;
	}

	private static ExistingReference findExistingReference(Program program, EquateSymbol convertSymbol) {
		SymbolEntry entry = convertSymbol.getFirstWholeMap();
		if (!(entry instanceof DynamicEntry dynamicEntry) || dynamicEntry.getHash() == 0) {
			return null;
		}
		Address convertAddr = convertSymbol.getPCAddress();
		long convertHash = dynamicEntry.getHash();
		Instruction instr = program.getListing().getInstructionAt(convertAddr);
		long value = convertSymbol.getValue();
		Boolean reconstructedMatch = null;
		ExistingReference selected = null;
		for (Equate equate : new LinkedHashSet<>(program.getEquateTable().getEquates(convertAddr))) {
			if (equate.getValue() != value) {
				continue;
			}
			String name = equate.getDisplayName();
			int format = EquateSymbol.convertName(name, value);
			if (format != convertSymbol.getConvert() ||
				(format == EquateSymbol.FORMAT_DEFAULT && !name.equals(convertSymbol.getName()))) {
				continue;
			}
			for (EquateReference ref : equate.getReferences(convertAddr)) {
				long hash = ref.getDynamicHashValue();
				if (hash == 0 && instr != null) {
					if (reconstructedMatch == null) {
						long[] hashes = DynamicHash.calcConstantHash(instr, value);
						reconstructedMatch = Arrays.stream(hashes).anyMatch(h -> h == convertHash);
						if (reconstructedMatch &&
							!Arrays.stream(hashes).allMatch(h -> h == convertHash)) {
							Msg.error(ConvertConstantEquateTask.class,
								"Listing equate applies to multiple constants");
							return null;
						}
					}
					if (!reconstructedMatch) {
						continue;
					}
				}
				else if (hash != convertHash) {
					continue;
				}
				if (selected != null) {
					Msg.error(ConvertConstantEquateTask.class, "Ambiguous equate reference");
					return null;
				}
				selected = new ExistingReference(equate, ref);
			}
		}
		if (selected == null) {
			Msg.error(ConvertConstantEquateTask.class, "Unable to identify the equate reference");
		}
		return selected;
	}

	static boolean removeExistingReference(Program program, EquateSymbol symbol) {
		ExistingReference selected = findExistingReference(program, symbol);
		if (selected == null) {
			return false;
		}
		return removeReference(program, selected.equate(), selected.reference());
	}

	/**
	 * Given the context, set up the task object that will execute the conversion.
	 * If the context is not suitable for a conversion, null is returned.
	 * @param context is the given context for the action
	 * @param action is the parent action for this task
	 * @return the task object or null
	 */
	protected static ConvertConstantEquateTask establishTask(DecompilerActionContext context,
			ConvertConstantAction action) {

		Scalar scalar = getConvertibleConstant(context, action.convertType);
		ConvertConstantEquateTask task = prepareTask(context, scalar, action.convertType, null);
		if (task == null) {
			return null;
		}
		String name = action.getEquateName(task.convertValue, context.getProgram());
		if (name == null) {
			return null;
		}
		task.convertName = name;
		if (task.altAddress != null) {
			task.altName = name;
		}
		return task;
	}

	static ConvertConstantEquateTask forEnum(DecompilerActionContext context, Scalar scalar,
			Enum enoom, long value) {
		EnumMember member = new EnumMember(enoom, value);
		ConvertConstantEquateTask task =
			prepareTask(context, scalar, EquateSymbol.FORMAT_DEFAULT, member);
		if (task == null) {
			return null;
		}
		if (task.previous != null && task.previous.equate().getValue() != value) {
			Varnode vn = context.getTokenAtCursor().getVarnode();
			DynamicHash hash = new DynamicHash(vn, context.getHighFunction());
			if (hash.getHash() == 0) {
				return null;
			}
			task.convertHash = hash.getHash();
			task.convertAddress = hash.getAddress();
			task.convertIndex = -1;
		}
		task.enumMember = member;
		return task;
	}

	private static ConvertConstantEquateTask prepareTask(DecompilerActionContext context,
			Scalar scalar, int convertType, EnumMember member) {
		Varnode varnode = context.getTokenAtCursor().getVarnode();
		HighSymbol symbol = varnode.getHigh().getSymbol();
		if (symbol instanceof EquateSymbol equateSymbol) {
			ExistingReference selected = findExistingReference(context.getProgram(), equateSymbol);
			if (selected == null) {
				return null;
			}
			EquateReference ref = selected.reference();
			ConvertConstantEquateTask task = new ConvertConstantEquateTask(context, null,
				ref.getAddress(), scalar, ref.getDynamicHashValue(), ref.getOpIndex());
			task.previous = selected;
			return task;
		}

		PcodeOp op = varnode.getLoneDescend();
		DynamicHash dynamicHash = member != null ? new DynamicHash(varnode, context.getHighFunction())
				: new DynamicHash(varnode, 0);
		long convertHash = dynamicHash.getHash();
		if (convertHash == 0) {
			return null;
		}
		Address convertAddr = dynamicHash.getAddress();
		if (op == null) {
			return new ConvertConstantEquateTask(context, null, convertAddr, scalar, convertHash, -1);
		}
		Program program = context.getProgram();
		ScalarMatch match = findScalarMatch(program, op.getSeqnum().getTarget(), scalar, member);
		// Don't create a named equate if the varnode and the instruction operand differ
		// as the name was selected specifically for the varnode
		if (match == null || (member == null && convertType == EquateSymbol.FORMAT_DEFAULT &&
			match.scalar.getValue() != scalar.getValue())) {
			return new ConvertConstantEquateTask(context, null, convertAddr, scalar, convertHash, -1);
		}

		ConvertConstantEquateTask task =
			new ConvertConstantEquateTask(context, null, convertAddr, match.scalar, convertHash, -1);

		// Try to set the equate on the instruction
		task.setAlternate(null, match.refAddr, match.opIndex,
			member == null ? match.scalar.getValue() : member.value());
		return task;
	}
}
