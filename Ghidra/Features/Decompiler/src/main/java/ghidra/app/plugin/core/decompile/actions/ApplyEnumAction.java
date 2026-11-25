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

import docking.action.MenuData;
import ghidra.app.plugin.core.decompile.*;
import ghidra.app.util.HelpTopics;
import ghidra.app.util.datatype.DataTypeSelectionDialog;
import ghidra.program.model.data.*;
import ghidra.program.model.data.Enum;
import ghidra.program.model.listing.Program;
import ghidra.program.model.pcode.*;
import ghidra.program.model.scalar.Scalar;
import ghidra.util.*;
import ghidra.util.data.DataTypeParser.AllowedDataTypes;
import ghidra.util.exception.InvalidInputException;

public class ApplyEnumAction extends AbstractDecompilerAction {
	private final DecompilePlugin plugin;

	public ApplyEnumAction(DecompilePlugin plugin) {
		super("Apply Enum");
		this.plugin = plugin;
		setPopupMenuData(new MenuData(new String[] { "Apply Enum..." }, "Decompile"));
		setHelpLocation(new HelpLocation(HelpTopics.DECOMPILER, "ActionApplyEnum"));
	}

	@Override
	protected boolean isEnabledForDecompilerContext(DecompilerActionContext context) {
		return getEnumScalar(context) != null;
	}

	private static Scalar getEnumScalar(DecompilerActionContext context) {
		Scalar scalar = ConvertConstantEquateTask.getConvertibleConstant(context,
			EquateSymbol.FORMAT_DEFAULT);
		if (scalar == null) {
			return null;
		}
		DataType type = context.getTokenAtCursor().getVarnode().getHigh().getDataType();
		if (type instanceof TypeDef typedef) {
			type = typedef.getBaseDataType();
		}
		if (type instanceof AbstractIntegerDataType integer && !(integer instanceof BooleanDataType)) {
			return scalar.isSigned() == integer.isSigned() ? scalar :
				new Scalar(scalar.bitLength(), scalar.getUnsignedValue(), integer.isSigned());
		}
		return (type instanceof Undefined || type == DataType.DEFAULT) ? scalar : null;
	}

	@Override
	protected void decompilerActionPerformed(DecompilerActionContext context) {
		Program program = context.getProgram();
		Scalar scalar = getEnumScalar(context);
		if (scalar == null) {
			return;
		}
		DataTypeSelectionDialog dialog = new DataTypeSelectionDialog(plugin.getTool(),
			program.getDataTypeManager(), -1, AllowedDataTypes.FIXED_LENGTH);
		dialog.setTitle("Apply Enum");
		plugin.getTool().showDialog(dialog);
		DataType chosen = dialog.getUserChosenDataType();
		if (chosen == null) {
			return;
		}
		try {
			if (!(chosen instanceof Enum enoom)) {
				throw new InvalidInputException("Choose an enum data type");
			}
			long value = getMemberValue(enoom, scalar);
			ConvertConstantEquateTask task =
				ConvertConstantEquateTask.forEnum(context, scalar, enoom, value);
			if (task == null) {
				throw new InvalidInputException("Could not identify the selected constant");
			}
			task.runTask();
		}
		catch (InvalidInputException e) {
			Msg.showError(this, plugin.getTool().getToolFrame(), "Apply Enum", e.getMessage());
		}
	}

	private static long getMemberValue(Enum enoom, Scalar scalar) throws InvalidInputException {
		long value = scalar.getValue();
		// An unsigned 64-bit scalar above Long.MAX_VALUE has a negative long representation.
		if ((value >= 0 || scalar.isSigned()) && enoom.contains(value)) {
			return value;
		}
		if (enoom.getLength() * Byte.SIZE == scalar.bitLength()) {
			value = scalar.getValue(!scalar.isSigned());
			if (enoom.contains(value)) {
				return value;
			}
		}
		throw new InvalidInputException("No member of " + enoom.getName() + " matches " + scalar);
	}
}
