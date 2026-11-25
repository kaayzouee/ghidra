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
import ghidra.app.decompiler.*;
import ghidra.app.plugin.core.decompile.DecompilerActionContext;
import ghidra.app.util.HelpTopics;
import ghidra.program.model.address.Address;
import ghidra.program.model.listing.Program;
import ghidra.program.model.pcode.*;
import ghidra.util.HelpLocation;
import ghidra.util.Msg;
import ghidra.util.exception.InvalidInputException;

/**
 * Remove a selected conversion or other equate set on a constant
 */
public class RemoveEquateAction extends AbstractDecompilerAction {

	public RemoveEquateAction() {
		super("Remove Equate");
		setHelpLocation(new HelpLocation(HelpTopics.DECOMPILER, "ActionRemoveEquate"));
		setPopupMenuData(new MenuData(new String[] { "Remove Convert/Equate" }, "Decompile"));
	}

	@Override
	protected boolean isEnabledForDecompilerContext(DecompilerActionContext context) {
		ClangToken tokenAtCursor = context.getTokenAtCursor();
		if (tokenAtCursor == null) {
			return false;
		}

		if (tokenAtCursor instanceof ClangCaseToken) {
			// Check for a conversion applied to case labels on a specific jumptable/switch
			PcodeOp switchOp = ((ClangCaseToken) tokenAtCursor).getSwitchOp();
			if (switchOp != null) {
				int format = JumpTable.getFormatOverride(context.getFunction(),
					switchOp.getSeqnum().getTarget());
				return (EquateSymbol.FORMAT_DEFAULT != format);
			}
			return false;
		}
		// Check for any Equate on a constant token
		if (!(tokenAtCursor instanceof ClangVariableToken)) {
			return false;
		}
		Varnode convertVn = tokenAtCursor.getVarnode();
		if (convertVn == null || !convertVn.isConstant()) {
			return false;
		}
		HighSymbol symbol = convertVn.getHigh().getSymbol();
		return (symbol instanceof EquateSymbol);
	}

	/**
	 * Remove the integer format override for a specific JumpTable
	 * @param context is the selected context
	 * @param opAddress is the address of the JumpTable branch site
	 */
	private void removeCaseOverride(DecompilerActionContext context, Address opAddress) {
		Program program = context.getProgram();
		int transaction = program.startTransaction("Remove Case Label Override");
		boolean commit = false;
		try {
			JumpTable.writeFormat(context.getFunction(), opAddress, transaction);
			commit = true;
		}
		catch (InvalidInputException e) {
			Msg.error(this, e);
		}
		finally {
			program.endTransaction(transaction, commit);
		}
	}

	@Override
	protected void decompilerActionPerformed(DecompilerActionContext context) {
		ClangToken tokenAtCursor = context.getTokenAtCursor();
		if (tokenAtCursor instanceof ClangCaseToken) {
			PcodeOp switchOp = ((ClangCaseToken) tokenAtCursor).getSwitchOp();
			removeCaseOverride(context, switchOp.getSeqnum().getTarget());
			return;
		}
		if (!(tokenAtCursor instanceof ClangVariableToken)) {
			return;
		}
		Varnode convertVn = tokenAtCursor.getVarnode();
		if (convertVn == null || !convertVn.isConstant()) {
			return;
		}
		HighSymbol convertSymbol = convertVn.getHigh().getSymbol();
		if (convertSymbol instanceof EquateSymbol symbol) {
			Program program = context.getProgram();
			int transaction = program.startTransaction("Remove Equate Reference");
			boolean commit = false;
			try {
				commit = ConvertConstantEquateTask.removeExistingReference(program, symbol);
			}
			finally {
				program.endTransaction(transaction, commit);
			}
			if (!commit) {
				Msg.showError(this, null, "Remove Equate",
					"Could not identify a unique equate reference.");
			}
		}
	}
}
