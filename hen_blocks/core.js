

// Reference: https://stackoverflow.com/questions/12303989/cartesian-product-of-multiple-arrays-in-javascript
function cartesianProduct(...a) {
    return a.reduce((a, b) => a.flatMap(d => b.map(e => [d, e].flat())), [[]]);
}

// REFERENCE: https://groups.google.com/g/blockly/c/eRFrGahCpxA
Blockly.blockRendering.RenderInfo.prototype.shouldStartNewRow_ = function (input, lastInput) {
    // If this is the first input, just add to the existing row.
    // That row is either empty or has some icons in it.
    if (!lastInput) {
        return false;
    }
    // A statement input or an input following one always gets a new row.
    if (input.type === Blockly.inputTypes.STATEMENT ||
        lastInput.type === Blockly.inputTypes.STATEMENT) {
        return true;
    }
    // Value inputs get new row if inputs are not inlined.
    if (input.type === Blockly.inputTypes.VALUE) {
        return !this.isInline;
    }
    // Dummy inputs get new row if name begins with "NEWLINE".
    // Otherwise dummy inputs get new row if inputs are not inlined.
    if (input.type === Blockly.inputTypes.DUMMY) {
        if (input.name.startsWith("NEWLINE")) {
            return true;
        } else {
            return !this.isInline;
        }
    }
    return false;
};

/**
 * This indicates whether traversal of blocks should be suspended.
 * One use case for this is when the user is currently editing a field. During editing, traversal is suspended to
 * prevent warning texts from being updated which may cause UI artifacts. Upon completion of editing, traversal is resumed
 * and references to the name will be automatically renamed.
 */
let isRenaming = false;
let fieldsToBeRenamed = [];

// HACK to make sure that traversal is done only after text field has been edited completely.
// Don't traverse during intermediate states.
// See https://github.com/google/blockly/issues/4350
function completeVariableRenaming(finalValue) {
    isRenaming = false;
    fieldsToBeRenamed = [];
    traverseBlocks();
}

function prepareToTraverseBlocks(event) {
    if (event.type === "viewport_change" || event.type === "drag") {
        return;
    }
    // console.log(event.type, event.element, event.name, isRenaming);

    let block;
    // Rename value
    if (event.type === "change" && event.element === "field" && event.name.startsWith("VAR")
        && (block = Blockly.getMainWorkspace().getBlockById(event.blockId))
        && block.getField(event.name) instanceof Blockly.FieldTextInput) {
        if (event.oldValue !== event.newValue) {
            if (!isRenaming) {
                isRenaming = true;

                // Only rename if the current variable being edited is not a name collision (doesn't have a warning)
                // Note that it is possible for the variable to be a name collision and not have a warning, but that would mean
                // that it is the first such instance, and so the renaming should happen.
                if (block.warning) {
                    return;
                }

                // Get all varFields and store into a list
                switch (block.type) {
                    case "intro":
                        traverseScopedVariablesToBeRenamed(block.getNextBlock(), event.oldValue, event.newValue);
                        break;
                    case "intro_pattern_identifier":
                        let nextBlock = block.getSurroundParent();
                        while (nextBlock && nextBlock.type !== "destruct") {
                            nextBlock = nextBlock.getSurroundParent();
                        }
                        nextBlock.getChildren(true).forEach(childBlock => traverseScopedVariablesToBeRenamed(childBlock, event.oldValue, event.newValue));
                        break;
                    case "binder":
                        traverseScopedVariablesToBeRenamed(block.getSurroundParent(), event.oldValue, event.newValue);
                        break;
                    case "inductive":
                    case "definition_or_fixpoint":
                    case "theorem":
                    case "constructor_definition":
                        traverseAllVariablesToBeRenamed(event.oldValue, event.newValue);
                        break;
                    case "case_identifier":
                        let nBlock = block.getSurroundParent();
                        let constrBlock;
                        while (nBlock && nBlock.type !== "match") {
                            if (nBlock.type === "case_constructor") {
                                constrBlock = nBlock;
                            }
                            nBlock = nBlock.getSurroundParent();
                        }
                        let i;
                        for (i = 0; i < nBlock.branchCount_; i++) {
                            const checkBlock = nBlock.getInputTargetBlock("CASE" + i);
                            if (checkBlock === constrBlock) {
                                break;
                            }
                        }
                        console.log(block);
                        console.log(constrBlock);
                        console.log(nBlock);
                        traverseScopedVariablesToBeRenamed(nBlock.getInputTargetBlock("RESULT" + i), event.oldValue, event.newValue);
                        break;
                    default:
                        console.warn("Illegal field change event detected");
                        isRenaming = false;
                        return;
                }
            }
            for (const field of fieldsToBeRenamed) {
                const options = field.getOptions(true);
                options[0] = [event.newValue, event.newValue];
                field.setValue(event.newValue);
            }
        }
    }
    // If renaming is turned on, we ignore all other events. If we don't ignore while renaming, there are change events from a variable dropdown
    // Such events are a side effect of the renaming and not user triggered. We want to suppress that so that the traverseBlocks() doesn't get triggered during text field editing.
    // This ensures that any change in warning text happens only after the user has finished editing (and focus is lost from the text field).
    // If the warning text changes while user is editing, there are text field artifacts.
    if (!isRenaming) {
        traverseBlocks();
    }
}

function traverseScopedVariablesToBeRenamed(block, oldValue, newValue) {
    if (!block) {
        return;
    }
    let varFields;
    switch (block.type) {
        case "destruct":
        case "induction":
        case "variable_dropdown":
        case "variable_dropdown_multiple":
        case "match":
        case "case_constructor":
            varFields = block.getVarFields();
            for (const varField of varFields) {
                if (varField.selectedOption_[0] === oldValue) {
                    fieldsToBeRenamed.push(varField);
                    // This prevents renaming from being propagated past a destruct/induction block, because such blocks
                    // remove a variable from the scope.
                    switch (block.type) {
                        case "destruct":
                        case "induction":
                            return;
                    }
                }
            }
            break;
        case "binder":
        case "definition_or_fixpoint":
            const typeFields = block.getTypeFields();
            for (const typeField of typeFields) {
                if (typeField.selectedOption_[0] === oldValue) {
                    fieldsToBeRenamed.push(typeField);
                }
            }
            break;
        default:
    }
    block.getChildren(true).forEach(childBlock => traverseScopedVariablesToBeRenamed(childBlock, oldValue, newValue));
}

function traverseAllVariablesToBeRenamed(oldValue, newValue) {
    for (const block of Blockly.getMainWorkspace().getTopBlocks(true)) {
        traverseScopedVariablesToBeRenamed(block, oldValue, newValue);
    }
}


// https://coq.inria.fr/refman/language/core/basic.html#lexical-conventions
const RESERVED_KEYWORDS = [
    '_', 'Axiom', 'CoFixpoint', 'Definition', 'Fixpoint', 'Hypothesis', 'Parameter', 'Prop', 'SProp', 'Set', 'Theorem',
    'Type', 'Variable', 'as', 'at', 'cofix', 'else', 'end', 'fix', 'for', 'forall', 'fun', 'if', 'in', 'let', 'match',
    'return', 'then', 'where', 'with', 'by', 'exists', 'exists2', 'using'];

const LOWERCASE_LETTERS = ["a","b","c","d","e","f","g","h","i","j","k","l","m","n","o","p","q","r","s","t","u","v","w","x","y","z"];
const UPPERCASE_LETTERS = ["A","B","C","D","E","F","G","H","I","J","K","L","M","N","O","P","Q","R","S","T","U","V","W","X","Y","Z"];
const ALLOWED_FIRST_LETTER = [...LOWERCASE_LETTERS, ...UPPERCASE_LETTERS, "_"];

const variableValidator = function(newValue) {
    // For subsequent letters, Coq only allows lowercase letter, uppercase letters, digits, "_", and "'".
    let modifiedValue = newValue.replace(/[^a-zA-Z0-9'_]/g, "");

    if (modifiedValue === "") {
        return null;
    }
    if (RESERVED_KEYWORDS.includes(modifiedValue)) {
        return null;
    }
    if (!ALLOWED_FIRST_LETTER.includes(modifiedValue[0])) {
        return null;
    }
    return modifiedValue;
};


function getConstructors(inductiveTypes) {
    const constructorArray = [];
    for (const [type, constructorMap] of inductiveTypes) {
        if (constructorMap.size >= 0) {
            constructorArray.push(...constructorMap);
        }
    }
    return new Map(constructorArray);
}

// Find variable collisions in Proofs (intro, destruct, induction, injection, revert)
// Find variable collisions in Theorem
// Find theorem name / inductive name / definition / fixpoint name collisions in global scope

// Do the onChange event here also --> set warning if identifier no longer exists (exact)


// Update dropdowns via separate function (exact) (extension)
// Renaming done via separate function (renameHypothesis)
/**
 * @member {Blockly.Block} block
 */
function traverseBlocks() {
    for (const block of Blockly.getMainWorkspace().getAllBlocks(true)) {
        block.setEnabled(true);
    }
    const blocks = Blockly.getMainWorkspace().getTopBlocks(true).filter(block => !block.isInsertionMarker_);
    if (blocks.length === 0) {
        return;
    }

    const allNames = ["nat", "bool", "S", "O", "true", "false", "Prop", "Type"];
    const theoremNames =  [];
    const definitionNames = [];
    // const inductiveNames = {
    //     "Prop": [],
    //     "nat": ["S", "O"],
    //     "bool": ["true", "false"],
    //     "Type": [],
    // };
    // TODO: Add more datatypes (https://coq.inria.fr/library/Coq.Init.Datatypes.html)
    const inductiveTypes = new Map([
        ["Prop", new Map()],
        ["nat", new Map([
            ["S", new Map([
                ["n'", "nat"],
            ])],
            ["O", new Map()]
        ])],
        ["bool", new Map([
            ["true", new Map()],
            ["false", new Map()]
        ])],
        ["Type", new Map()]
    ]);
    const constructorNames = [];

    // Traverse all top-level blocks first and record down identifiers so that we can prevent name conflicts later on.
    for (const block of blocks) {
        switch (block.type) {
            case "inductive":
            case "definition_or_fixpoint":
            case "theorem":
                const name = block.getFieldValue("VAR");
                if (allNames.includes(name)) {
                    block.setWarningText(`"${name}" has already been defined.`);
                } else {
                    block.setWarningText(null);
                    allNames.push(name);
                }
                break;
        }
        switch (block.type) {
            case "inductive":
                const localConstructorNames = block.getConstructorNames(true, allNames);
                allNames.push(...localConstructorNames);
                break;
        }
    }



    for (const block of blocks) {
        let nextBlock;
        switch (block.type) {
            case "theorem":
                nextBlock = block.getInputTargetBlock('PROPOSITION');
                traverseTheorem(nextBlock, [], theoremNames, definitionNames, inductiveTypes, constructorNames, allNames);

                const proofBlock = block.getNextBlock();
                traverseProof(proofBlock, [], theoremNames, definitionNames, inductiveTypes, constructorNames, allNames);

                const theoremName = block.getFieldValue("VAR");
                if (!block.warning) { // Warning occurs only if it's a duplicate name
                    console.assert(!theoremNames.includes(theoremName));
                    theoremNames.push(theoremName);
                }
                break;
            case "definition_or_fixpoint":
                const definitionName = block.getFieldValue("VAR");
                const isFixpoint = block.getFieldValue("COMMAND") === "Fixpoint";
                if (!block.warning) { // Warning occurs only if it's a duplicate name
                    console.assert(!definitionNames.includes(definitionName));
                    if (isFixpoint) {
                        definitionNames.push(definitionName);
                    }
                }
                block.setTypeDropdown([...inductiveTypes.keys()].map(value => [value, value]));
                // TODO: Handle new types from definition and propagate down. Consider shifting this to traverseDefinition?
                const [localIdentifiers, newTypes] = block.getIdentifiers(true, allNames);
                const newInductiveTypes = new Map(inductiveTypes);
                for (const type of newTypes) {
                    newInductiveTypes.set(type, new Map());
                }
                nextBlock = block.getInputTargetBlock('EXPRESSION');
                traverseDefinition(nextBlock, localIdentifiers, theoremNames, definitionNames, newInductiveTypes, constructorNames, allNames);

                // If we have not added the definition name (e.g. non-recursive), add it now.
                if (!block.warning && !isFixpoint) {
                    console.assert(!definitionNames.includes(definitionName));
                    definitionNames.push(definitionName);
                }
                break;
            case "inductive":
                const inductiveName = block.getFieldValue("VAR");
                const localConstructorNames = block.getConstructorNames(false);

                if (!block.warning) {
                    constructorNames.push(...localConstructorNames);
                    inductiveTypes.set(inductiveName, new Map());
                }

                block.setTypeDropdown([...inductiveTypes.keys()].map(value => [value, value]));
                // TODO: We want to get list of arguments for each constructor, and the corresponding type for each argument
                for (let i = 0; i < block.branchCount_; i++) {
                    const constrBlock = block.getInputTargetBlock("BRANCH" + i);
                    if (!constrBlock) {
                        continue;
                    }
                    const constrName = constrBlock.getFieldValue("VAR");
                    const [constructorIdentifiers, _] = constrBlock.getIdentifiers(true, allNames);
                    const constructorIdentifiersArray = constructorIdentifiers.map(value => [value, ""]);
                    if (!block.warning) {
                        inductiveTypes.get(inductiveName).set(constrName, new Map(constructorIdentifiersArray));
                    }
                }
                break;
            // case "exact":
            // case "intro":
            // case "split":
            // case "destruct":
            // case "induction":
            // case "proof":
            //     traverseProof(block, []);
            //     disableChildBlocks(block);
            //     break;
            // case "variable_dropdown":
            // case "variable_dropdown_multiple":
            // case "forall":
            // case "exists":
            //     traverseTheorem(block, [], theoremNames, definitionNames, inductiveTypes, constructorNames, allNames);
            //     disableChildBlocks(block);
            //     break;
            default:
                disableChildBlocks(block);
        }
    }
}

function traverseDefinition(block, localNames, theoremNames, definitionNames, inductiveTypes, constructorNames, allNames) {
    if (!block) {
        return;
    }
    const newLocalNames = [...localNames];
    const newAllNames = [...allNames];
    const newInductiveTypes = new Map(inductiveTypes); // I can get away with doing this because the arrays inside this object won't be changed during the traversal.

    switch (block.type) {
        case "forall":
        case "exists":
            // Get names and types from each binder
            block.setTypeDropdown([...inductiveTypes.keys()].map(value => [value, value]));
            // TODO: Refactor to combine the above and below line into one function: getIdentifiersAndSetTypeDropdown()
            const [localIdentifiers, newTypes] = block.getIdentifiers(true, allNames);
            newLocalNames.push(...localIdentifiers);
            newAllNames.push(...localIdentifiers);
            for (const type of newTypes) {
                newInductiveTypes.set(type, new Map());
            }
            break;
        case "variable_dropdown":
        case "variable_dropdown_multiple":
            const varFields = block.getVarFields();
            const warnings = new Set();
            for (const varField of varFields) {
                const selectedOption = varField.getValue();
                if (selectedOption === "[Select variable]") {
                    warnings.add("Please select a variable.");
                } else if (!localNames.includes(selectedOption) && !theoremNames.includes(selectedOption) && !definitionNames.includes(selectedOption) && !constructorNames.includes(selectedOption)) {
                    warnings.add("Please ensure the selected variable has been defined.");
                }
                const names = [...localNames, ...definitionNames, ...constructorNames, ...theoremNames];
                if (names.length === 0) {
                    varField.menuGenerator_ = [["[Select variable]", "[Select variable]"]];
                } else {
                    varField.menuGenerator_ = names.map(value => [value, value]);
                }
            }
            if (warnings.size === 0) {
                block.setWarningText(null);
            } else {
                block.setWarningText([...warnings].join("\n"));
            }
            break;
    }
    switch (block.type) {
        case "match":
            const constructors = getConstructors(inductiveTypes);
            const caseConstrBlocks = block.getCaseConstrBlocks();
            const selectedConstructors = [];
            for (const caseConstrBlock of caseConstrBlocks) {
                const constrField = caseConstrBlock.getField("VAR");
                constrField.menuGenerator_ = [...constructors.keys()].map(value => [value, value]);

                const value = constrField.getValue();
                if (value === "[Select constructor]" || !constructors.has(value)) {
                    caseConstrBlock.updateShape_(0);
                } else {
                    const argMap = constructors.get(value);
                    caseConstrBlock.updateShape_(argMap.size);
                }
                const constrWarnings = new Set();

                if (selectedConstructors.includes(value)) {
                    constrWarnings.add("Pattern has already been used");
                }
                if (!constructors.has(value)) {
                    constrWarnings.add("Please ensure the selected constructor has been defined.");
                }
                if (constrWarnings.size === 0) {
                    caseConstrBlock.setWarningText(null);
                } else {
                    caseConstrBlock.setWarningText([...constrWarnings].join("\n"));
                }

                selectedConstructors.push(value);
            }




            const varFields = block.getVarFields();
            const warnings = new Set();
            for (const varField of varFields) {
                const selectedOption = varField.getValue();
                if (selectedOption === "[Select variable]") {
                    warnings.add("Please select a variable.");
                } else if (!newLocalNames.includes(selectedOption)) {
                    warnings.add("Please ensure the selected variable has been defined.");
                }
                const names = [...localNames];
                if (names.length === 0) {
                    varField.menuGenerator_ = [["[Select variable]", "[Select variable]"]];
                } else {
                    varField.menuGenerator_ = names.map(value => [value, value]);
                }
            }
            if (warnings.size === 0) {
                block.setWarningText(null);
            } else {
                block.setWarningText([...warnings].join("\n"));
            }

            for (let i = 0; i < block.branchCount_; i++) {
                const caseBlock = block.getInputTargetBlock("CASE" + i);
                if (!caseBlock) {
                    continue;
                }
                const caseIdentifiers = caseBlock.getIdentifiers(true, newAllNames);
                const resultBlock = block.getInputTargetBlock("RESULT" + i);
                traverseDefinition(resultBlock, [...newLocalNames, ...caseIdentifiers], theoremNames, definitionNames, newInductiveTypes, constructorNames, [...newAllNames, ...caseIdentifiers])
            }
            return;
    }
    block.getChildren(true).forEach(childBlock => traverseDefinition(childBlock, newLocalNames, theoremNames, definitionNames, newInductiveTypes, constructorNames, newAllNames));
}

// I CANNOT ENFORCE TYPE CHECKING DUE TO SCOPED NATURE OF VARIABLE DROPDOWN BLOCK
// (e.g. if I want to drag a variable into a _ + _ block, it cannot check beforehand whether the variables is a natural number.
function traverseTheorem(block, localNames, theoremNames, definitionNames, inductiveTypes, constructorNames, allNames) {
    if (!block) {
        return;
    }
    const newLocalNames = [...localNames];
    const newAllNames = [...allNames];
    const newInductiveTypes = new Map(inductiveTypes); // I can get away with doing this because the arrays inside this object won't be changed during the traversal.
    switch (block.type) {
        case "forall":
        case "exists":
            // Get names and types from each binder
            block.setTypeDropdown([...inductiveTypes.keys()].map(value => [value, value]));
            const [localIdentifiers, newTypes] = block.getIdentifiers(true, newAllNames);
            newLocalNames.push(...localIdentifiers);
            newAllNames.push(...localIdentifiers);
            for (const type of newTypes) {
                newInductiveTypes.set(type, new Map());
            }
            break;
        case "variable_dropdown":
        case "variable_dropdown_multiple":
            const dropdownOptions =  [...localNames, ...definitionNames, ...constructorNames, ...theoremNames];

            const varFields = block.getVarFields();
            const warnings = new Set();
            for (const varField of varFields) {
                const selectedOption = varField.getValue();
                if (selectedOption === "[Select variable]") {
                    warnings.add("Please select a variable.");
                } else if (!dropdownOptions.includes(selectedOption)) {
                    warnings.add("Please ensure the selected variable has been defined.");
                }
                if (dropdownOptions.length === 0) {
                    varField.menuGenerator_ = [["[Select variable]", "[Select variable]"]];
                } else {
                    varField.menuGenerator_ = dropdownOptions.map(value => [value, value]);
                }
            }
            if (warnings.size === 0) {
                block.setWarningText(null);
            } else {
                block.setWarningText([...warnings].join("\n"));
            }
            break;
        default:
    }
    block.getChildren(true).forEach(childBlock => traverseTheorem(childBlock, newLocalNames, theoremNames, definitionNames, newInductiveTypes, constructorNames, newAllNames));
}

/**
 *
 * @param {!Blockly.Block} block
 */
function traverseProof(block, localNames, theoremNames, definitionNames, inductiveTypes, constructorNames, allNames) {
    if (!block) {
        return;
    }
    // console.log(block.type, names);
    const newLocalNames = [...localNames];
    const newAllNames = [...allNames];

    // VARIABLE DROPDOWN
    // Check whether selected variable is valid
    // Update dropdown options
    let dropdownOptions =  [...localNames, ...definitionNames, ...constructorNames, ...theoremNames];
    switch (block.type) {
        case "induction":
        case "destruct":
            dropdownOptions = [...localNames];
            // fallthrough
        case "variable_dropdown":
        case "variable_dropdown_multiple":
            if (block.getSurroundParent().type === "revert" || block.getSurroundParent().type === "contradiction" || block.getSurroundParent().type === "discriminate") {
                dropdownOptions = [...localNames];
            }
            if (block.getSurroundParent().type === "unfold") {
                dropdownOptions = [...definitionNames, ...theoremNames];
            }

            const varFields = block.getVarFields();
            const warnings = new Set();
            for (const varField of varFields) {
                const selectedOption = varField.getValue();
                if (selectedOption === "[Select variable]") {
                    warnings.add("Please select variable.");
                } else if (!dropdownOptions.includes(selectedOption)) {
                    warnings.add("Please ensure the selected variable has been defined.");
                }
                if (dropdownOptions.length === 0) {
                    varField.menuGenerator_ = [["[Select variable]", "[Select variable]"]];
                } else {
                    varField.menuGenerator_ = dropdownOptions.map(value => [value, value]);
                }
            }
            if (warnings.size === 0) {
                block.setWarningText(null);
            } else {
                block.setWarningText([...warnings].join("\n"));
            }
            break;
    }

    // DEFINING VARIABLES
    // Check whether variable has been defined before
    // Update name list with newly defined variables / variables that have been destructed
    let selectedOption, index;
    switch (block.type) {
        case "revert":
            const varBlock = block.getInputTargetBlock("VAR");
            if (varBlock) {
                selectedOption = varBlock.getFieldValue("VAR");
                if (localNames.includes(selectedOption)) {
                    traverseProof(varBlock, newLocalNames, theoremNames, definitionNames, inductiveTypes, constructorNames, newAllNames);
                    index = localNames.indexOf(selectedOption);
                    newLocalNames.splice(index, 1);
                    index = allNames.indexOf(selectedOption);
                    newAllNames.splice(index, 1);
                    traverseProof(block.getNextBlock(), newLocalNames, theoremNames, definitionNames, inductiveTypes, constructorNames, newAllNames);
                    return;
                }
            }
            break;
        case "intro":
            const name = block.getFieldValue("VAR");
            if (newAllNames.includes(name)) {
                block.setWarningText(`"${name}" has already been defined.`);
            } else {
                block.setWarningText(null);
                newLocalNames.push(name);
                newAllNames.push(name);
            }
            break;
        case "induction":
        case "destruct":
            if (!block.isInsertionMarker_) {
                const patternBlock = block.getInputTargetBlock("PATTERN");
                let targetCount = patternBlock?.getNumBranches() ?? 0;
                if (targetCount === 1) {
                    targetCount = 0;
                }
                block.updateShape_(targetCount);
            }



            selectedOption = block.getFieldValue("VAR");
            index = localNames.indexOf(selectedOption);
            newLocalNames.splice(index, 1);
            index = allNames.indexOf(selectedOption);
            newAllNames.splice(index, 1);
            const identifiers = block.getIdentifiersFromIntroPattern(true, newAllNames);
            if (identifiers.length > 0) {
                if (block.branchCount_ === 0) {
                    console.assert(identifiers.length === 1);
                    newLocalNames.push(...identifiers[0]);
                    newAllNames.push(...identifiers[0]);
                } else {
                    console.assert(identifiers.length === block.branchCount_);
                    for (let i = 0; i < block.branchCount_; i++) {
                        const branchBlock = block.getInputTargetBlock("STATEMENTS" + i);
                        const branchNames = [...newLocalNames, ...identifiers[i]];
                        const branchAllNames = [...newAllNames, ...identifiers[i]];
                        traverseProof(branchBlock, branchNames, theoremNames, definitionNames, inductiveTypes, constructorNames, branchAllNames);
                    }
                    return;
                }
            }
            break;
        default:
    }

    block.getChildren(true).forEach(childBlock => traverseProof(childBlock, newLocalNames, theoremNames, definitionNames, inductiveTypes, constructorNames, newAllNames));
}


function disableChildBlocks(block) {
    if (!block) {
        return;
    }
    block.setEnabled(false);
    block.getChildren(true).forEach(childBlock => disableChildBlocks(childBlock));
}
