import {createMinusField} from './field_minus.js';
import {createPlusField} from './field_plus.js';

// https://github.com/google/blockly-samples/blob/master/plugins/block-plus-minus/src/if.js

const forallExistsMutator = {
    binderCount_: 0,
    MIN_COUNT: 0,

    /**
     * Creates XML to represent the number of inputs.
     * @return {Element} XML storage element.
     * @this {Blockly.Block}
     */
    mutationToDom: function () {
        const container = Blockly.utils.xml.createElement('mutation');
        container.setAttribute('binderCount', this.binderCount_);
        return container;
    },

    /**
     * Parses XML to restore the split inputs.
     * @param {!Element} xmlElement XML storage element.
     * @this {Blockly.Block}
     */
    domToMutation: function (xmlElement) {
        const targetCount = parseInt(xmlElement.getAttribute('binderCount'), 10);
        this.updateShape_(targetCount);
    },

    /**
     * Adds inputs to the block until the block matches the target split count.
     * @param {number} targetCount The target number of inputs.
     * @this {Blockly.Block}
     * @private
     */
    updateShape_: function (targetCount) {
        while (this.binderCount_ < targetCount) {
            this.addBinder_(false);
        }
        while (this.binderCount_ > targetCount) {
            this.removeBinder_();
        }
    },

    /**
     * Callback for the plus field. Adds an input to the block.
     */
    plus: function () {
        this.addBinder_();
    },

    /**
     * Callback for the minus field. Triggers "removing" the input at the specific
     * index.
     * @see removeInput_
     * @param {number} index The index of the input to "remove".
     * @this {Blockly.Block}
     */
    minus: function (index) {
        if (this.binderCount_ === this.MIN_COUNT) {
            return;
        }
        this.removeBinder_(index);
    },

    /**
     * Adds an input to the bottom of the block.
     * @this {Blockly.Block}
     * @private
     */
    addBinder_: function (shouldAddBlock = true) {
        // Because inputs are 1-indexed we increment first, decrement last.
        this.binderCount_++;
        const binderInput = this.appendValueInput('BINDER' + this.binderCount_)
            .setCheck('Binder')
            .appendField(createMinusField(this.binderCount_), 'MINUS' + this.binderCount_)
            .setAlign(Blockly.ALIGN_RIGHT);
        this.moveInputBefore("PROPOSITION", null);

        if (shouldAddBlock) {
            const binderBlock = Blockly.getMainWorkspace().newBlock("binder");
            binderBlock.initSvg();
            binderBlock.render();
            binderInput.connection.connect(binderBlock.outputConnection);
        }
    },

    /**
     * Appears to remove the input at the given index. Actually shifts attached
     * blocks and then removes the input at the bottom of the block. This is to
     * make sure the inputs are always BINDER0, BINDER1, etc. with no gaps.
     * @param {?number=} index The index of the input to "remove", or undefined
     *     to remove the last input.
     * @this {Blockly.Block}
     * @private
     */
    removeBinder_: function (index = undefined) {
        // The strategy for removing a part at an index is to:
        //  - Kick any blocks connected to the relevant inputs.
        //  - Move all connect blocks from the other inputs up.
        //  - Remove the last input.
        // This makes sure all of our indices are correct.

        // TODO: After refreshing, the minus buttons somehow lose their numbering. Pressing button causes disconnection but not deletion.

        if (index !== undefined) {
            const inputs = this.inputList;
            let connection = inputs[index].connection;
            if (connection.isConnected()) {
                connection.targetBlock().dispose();
            }
            for (let i = index + 1, input; (input = this.inputList[i]); i++) {
                const targetConnection = input.connection.targetConnection;
                if (targetConnection) {
                    this.inputList[i - 1].connection.connect(targetConnection);
                }
            }
        }

        const binderBlock = this.getInputTargetBlock("BINDER" + this.binderCount_);
        if (binderBlock) {
            binderBlock.dispose();
        }
        this.removeInput('BINDER' + this.binderCount_);
        this.bumpNeighbours();
        // Because else-if inputs are 1-indexed we increment first, decrement last.
        this.binderCount_--;
    },

    getIdentifiers: function (setWarnings, names) {
        const identifiers = [];
        const newTypes = [];
        for (let i = 0; i <= this.binderCount_; i++) {
            const binderInput = this.getInput("BINDER" + i);
            if (binderInput.connection.isConnected()) {
                const binderBlock = binderInput.connection.targetBlock();
                binderBlock.addTypeDropdown(newTypes.map(value => [value, value]));

                const [binderIdentifiers, binderNewTypes] = binderBlock.getIdentifiers();
                if (setWarnings) {
                    const uniqueIdentifiers = new Set(binderIdentifiers);
                    const selectedTypes = []
                    for (let j = 0; j < binderBlock.typeCount_; j++) {
                        const selectedType = binderBlock.getFieldValue("TYPE" + j);
                        selectedTypes.push(selectedType);
                    }
                    const warnings = new Set();

                    if (selectedTypes.some(selectedType => !names.includes(selectedType))) {
                        warnings.add("Please ensure the selected type has been defined.")
                    }

                    if (uniqueIdentifiers.size !== binderIdentifiers.length
                        || binderIdentifiers.some(identifier => identifiers.includes(identifier) || names.includes(identifier))) {
                        warnings.add("Duplicate variable names.");
                    }

                    if (warnings.size === 0) {
                        binderBlock.setWarningText(null);
                    } else {
                        binderBlock.setWarningText([...warnings].join("\n"));
                    }
                }
                const typesToAdd = binderNewTypes.filter(type => !names.includes(type) && !newTypes.includes(type));
                newTypes.push(...typesToAdd);
                identifiers.push(...binderIdentifiers);
            }
        }
        const filteredIdentifiers = [...new Set(identifiers)].filter(identifier => !names.includes(identifier)); // Sets in JavaScript maintain insertion order
        return [filteredIdentifiers, newTypes];
    },

    setTypeDropdown: function (options) {
        for (let i = 0; i <= this.binderCount_; i++) {
            const block = this.getInputTargetBlock("BINDER" + i);
            if (block) {
                block.setTypeDropdown(options);
            }
        }
    }
};

const forallExistsMutatorHelper = function () {
    this.getInput('BINDER0').insertFieldAt(1, createPlusField(), 'PLUS');
};

Blockly.Extensions.unregister('forall_exists_mutator');
Blockly.Extensions.registerMutator('forall_exists_mutator', forallExistsMutator, forallExistsMutatorHelper);


const binderDialogMutator = {
    varCount_: 1,

    mutationToDom: function () {
        const container = Blockly.utils.xml.createElement('mutation');
        container.setAttribute('varCount', this.varCount_);
        return container;
    },
    domToMutation: function (xmlElement) {
        this.varCount_ = parseInt(xmlElement.getAttribute('varCount'), 10);
        this.updateShape_();
    },

    decompose: function (workspace) {
        const containerBlock = workspace.newBlock('binder_dialog_container');
        containerBlock.initSvg();
        let connection = containerBlock.getInput('STACK').connection;
        for (let i = 1; i <= this.varCount_; i++) {
            const itemBlock = workspace.newBlock('binder_dialog_var');
            itemBlock.initSvg();
            connection.connect(itemBlock.previousConnection);
            connection = itemBlock.nextConnection;
        }
        return containerBlock;
    },
    compose: function (containerBlock) {
        // First we get the first sub-block (which represents an input on our main block).
        let itemBlock = containerBlock.getInputTargetBlock('STACK');

        this.varCount_ = 0;
        while (itemBlock && !itemBlock.isInsertionMarker()) {  // Ignore insertion markers!
            this.varCount_++;
            itemBlock = itemBlock.nextConnection &&
                itemBlock.nextConnection.targetBlock();
        }

        // Then we update the shape of our block (removing or adding inputs as necessary).
        // `this` refers to the main block.
        this.updateShape_();
    },
    /**
     * Modify this block to have the correct number of inputs.
     * @private
     * @this {Blockly.Block}
     */
    updateShape_: function () {
        let i;
        // Add new inputs.
        for (i = 0; i < this.varCount_; i++) {
            if (!this.getField('VAR' + i)) {
                this.inputList[0].insertFieldAt(i, new Blockly.FieldTextInput("var" + i, variableValidator), 'VAR' + i);
            }
        }
        // Remove deleted inputs.
        while (this.getField('VAR' + i)) {
            this.inputList[0].removeField('VAR' + i);
            i++;
        }
    }
};

// See Blockly.Constants.Logic.CONTROLS_IF_MUTATOR_MIXIN
// See lists.js also: Blockly.Blocks['lists_create_with'].updateShape_

Blockly.Extensions.unregister('binder_dialog_mutator');
Blockly.Extensions.registerMutator('binder_dialog_mutator', binderDialogMutator, undefined, ["binder_dialog_var"]);


// TODO:
// Allow    list nat
// Allow    (type -> type) -> type
// Allow    forall (V : Type), list V -> nat
Blockly.Blocks['binder'] = {
    varCount_: 1,
    typeCount_: 1,
    MIN_COUNT: 1,

    init: function () {
        const nameField = new Blockly.FieldTextInput("var0", variableValidator);
        nameField.setSpellcheck(false);
        // HACK to make sure that traversal is done only after text field has been edited completely.
        // Don't traverse during intermediate states.
        // See https://github.com/google/blockly/issues/4350
        nameField.onFinishEditing_ = completeVariableRenaming;

        const typeField = new Blockly.FieldDropdown([
            ["Prop", "Prop"],
            ["nat", "nat"],
            ["bool", "bool"],
            ["Type", "Type"]
        ]);

        this.appendDummyInput("DUMMY")
            .appendField(createPlusField("VAR"), 'PLUS_VAR')
            .appendField(nameField, 'VAR0')
            .appendField(":")
            .appendField(createPlusField("TYPE"), 'PLUS_TYPE')
            .appendField(typeField, "TYPE0");

        this.setColour(COLOUR_VAR);
        this.setOutput(true, "Binder");
        this.setMovable(false);
        this.setDeletable(false);
    },

    /**
     * Creates XML to represent the number of inputs.
     * @return {Element} XML storage element.
     * @this {Blockly.Block}
     */
    mutationToDom: function () {
        const container = typeDropdownMutationToDom.call(this);
        container.setAttribute('varCount', this.varCount_);
        container.setAttribute('typeCount', this.typeCount_);
        return container;
    },

    /**
     * Parses XML to restore the split inputs.
     * @param {!Element} xmlElement XML storage element.
     * @this {Blockly.Block}
     */
    domToMutation: function (xmlElement) {
        const targetVarCount = parseInt(xmlElement.getAttribute('varCount'), 10);
        const targetTypeCount = parseInt(xmlElement.getAttribute('typeCount'), 10);
        this.updateShape_(targetVarCount, targetTypeCount);
        typeDropdownDomToMutation.call(this, xmlElement);
    },

    /**
     * Adds inputs to the block until the block matches the target split count.
     * @this {Blockly.Block}
     * @private
     */
    updateShape_: function (targetVarCount, targetTypeCount) {
        while (this.varCount_ < targetVarCount) {
            this.addVar_();
        }
        while (this.varCount_ > targetVarCount) {
            this.removeVar_();
        }
        while (this.typeCount_ < targetTypeCount) {
            this.addType_();
        }
        while (this.typeCount_ > targetTypeCount) {
            this.removeType_();
        }
    },

    /**
     * Callback for the plus field. Adds an input to the block.
     */
    plus: function (args) {
        if (args === "VAR") {
            this.addVar_();
        } else if (args === "TYPE") {
            this.addType_();
        } else {
            console.warn("Unrecognised args for the plus field:", args);
        }
    },

    /**
     * Callback for the minus field. Triggers "removing" the input at the specific
     * index.
     * @see removeInput_
     * @this {Blockly.Block}
     */
    minus: function (args) {
        if (args === "VAR") {
            if (this.varCount_ === this.MIN_COUNT) {
                return;
            }
            this.removeVar_();
        } else if (args === "TYPE") {
            if (this.typeCount_ === this.MIN_COUNT) {
                return;
            }
            this.removeType_();
        } else {
            console.warn("Unrecognised args for the minus field:", args);
        }
    },

    /**
     * Adds an input to the bottom of the block.
     * @this {Blockly.Block}
     * @private
     */
    addVar_: function () {
        if (this.varCount_ === this.MIN_COUNT) {
            this.inputList[0].insertFieldAt(1, createMinusField("VAR"), 'MINUS_VAR');
        }
        const nameField = new Blockly.FieldTextInput("var" + this.varCount_, variableValidator);
        nameField.onFinishEditing_ = completeVariableRenaming;
        this.inputList[0].insertFieldAt(this.varCount_ + 2, nameField, 'VAR' + this.varCount_);
        this.varCount_++;
    },
    removeVar_: function (index = undefined) {
        this.varCount_--;
        if (this.varCount_ === this.MIN_COUNT) {
            this.inputList[0].removeField("MINUS_VAR");
        }
        this.inputList[0].removeField('VAR' + this.varCount_);
    },
    getIdentifiers: function () {
        const identifiers = [];
        for (let i = 0; i < this.varCount_; i++) {
            const value = this.getFieldValue("VAR" + i);
            identifiers.push(value);
        }
        if (this.getFieldValue("TYPE0") === "Type" && this.typeCount_ === 1) {
            return [identifiers, identifiers];
        } else {
            return [identifiers, []];
        }
    },
    addTypeDropdown: function (newOptions) {
        for (let i = 0; i < this.typeCount_; i++) {
            const field = this.getField("TYPE" + i);
            field.menuGenerator_ = [...field.getOptions(true), ...newOptions]
        }
    },
    setTypeDropdown: function (options) {
        for (let i = 0; i < this.typeCount_; i++) {
            const field = this.getField("TYPE" + i);
            field.menuGenerator_ = options;
        }
    },
    addType_: function () {
        if (this.typeCount_ === this.MIN_COUNT) {
            this.inputList[0].insertFieldAt(3 + this.varCount_ + (this.varCount_ === this.MIN_COUNT ? 0 : 1),
                createMinusField("TYPE"), 'MINUS_TYPE');
        }
        const typeField = new Blockly.FieldDropdown([
            ["Prop", "Prop"],
            ["nat", "nat"],
            ["bool", "bool"],
            ["Type", "Type"]
        ]);
        this.inputList[0]
            .appendField("➝", "ARROW" + this.typeCount_)
            .appendField(typeField, 'TYPE' + this.typeCount_);
        this.typeCount_++;
    },
    removeType_: function (index = undefined) {
        this.typeCount_--;
        if (this.typeCount_ === this.MIN_COUNT) {
            this.inputList[0].removeField("MINUS_TYPE");
        }
        this.inputList[0].removeField("ARROW" + this.typeCount_);
        this.inputList[0].removeField('TYPE' + this.typeCount_);
    },
    getTypeFields: function () {
        const fields = [];
        for (let i = 0; i < this.typeCount_; i++) {
            const field = this.getField("TYPE" + i);
            fields.push(field);
        }
        return fields;
    }
};

Blockly.Blocks['induction'] = {
    branchCount_: 0,
    MIN_COUNT: 0,

    init: function () {
        this.appendDummyInput()
            .appendField("induction")
            .appendField(new Blockly.FieldDropdown([["[Select variable]", "[Select variable]"]]), "VAR")
            .appendField("as");
        this.appendValueInput("PATTERN")
            .setCheck("DisjunctionPattern");
        this.setColour(COLOUR_TACTICS);
        this.setPreviousStatement("Tactic");
        this.setInputsInline(true);
    },
    mutationToDom: function () {
        const container = varDropdownMutationToDom.call(this);
        container.setAttribute('branchCount', this.branchCount_);
        return container;
    },
    domToMutation: function (xmlElement) {
        varDropdownDomToMutation.call(this, xmlElement);
        const targetCount = parseInt(xmlElement.getAttribute('branchCount'), 10);
        this.updateShape_(targetCount);
    },
    onchange: function (event) {
        // See Blockly.Blocks['destruct'].onChange
        if (!this.isInsertionMarker_) {
            const block = this.getInputTargetBlock("PATTERN");
            let targetCount = block?.getNumBranches() ?? 0;
            this.updateShape_(targetCount);
        }
    },
    updateShape_: function (targetCount) {
        while (this.branchCount_ < targetCount) {
            this.addBranch_();
        }
        while (this.branchCount_ > targetCount) {
            this.removeBranch_();
        }
    },
    addBranch_: function () {
        this.appendStatementInput("STATEMENTS" + this.branchCount_);
        this.branchCount_++;
    },
    removeBranch_: function () {
        this.branchCount_--;
        const connection = this.getInput("STATEMENTS" + this.branchCount_).connection;
        if (connection.isConnected()) {
            connection.disconnect();
            this.bumpNeighbours();
        }
        this.removeInput("STATEMENTS" + this.branchCount_);
    },
    getIdentifiersFromIntroPattern: function (setWarnings, names) {
        const block = this.getInputTargetBlock("PATTERN");
        return block ? block.getIdentifiersFromIntroPattern(setWarnings, names) : [];
    },
    getVarFields: function () {
        return [this.getField("VAR")];
    }
}

Blockly.Blocks['multiple_identifier'] = {
    varCount_: 1,
    MIN_COUNT: 0,

    init: function () {
        this.appendDummyInput("BUTTONS")
            .appendField(createPlusField(), 'PLUS')
            .appendField(createMinusField(), 'MINUS');
        this.appendValueInput("VAR0")
            .setCheck(["IntroPattern", "IntroPatternIdentifier"]);
        this.setColour(COLOUR_TACTICS);
        this.setOutput(true, "MultipleIdentifier");
        this.setInputsInline(true);
    },

    mutationToDom: function () {
        const container = Blockly.utils.xml.createElement('mutation');
        container.setAttribute('varCount', this.varCount_);
        return container;
    },
    domToMutation: function (xmlElement) {
        const targetCount = parseInt(xmlElement.getAttribute('varCount'), 10);
        this.updateShape_(targetCount);
    },
    updateShape_: function (targetCount) {
        while (this.varCount_ < targetCount) {
            this.addVar_();
        }
        while (this.varCount_ > targetCount) {
            this.removeVar_();
        }
    },
    plus: function () {
        this.addVar_();
    },
    minus: function () {
        if (this.varCount_ === this.MIN_COUNT) {
            return;
        }
        this.removeVar_();
    },
    addVar_: function () {
        if (this.varCount_ === this.MIN_COUNT) {
            this.getInput("BUTTONS")
                .appendField(createMinusField(), 'MINUS');
        }
        this.appendValueInput("VAR" + this.varCount_)
            .setCheck(["IntroPattern", "IntroPatternIdentifier"]);
        this.varCount_++;

    },
    removeVar_: function () {
        this.varCount_--;
        const connection = this.getInput("VAR" + this.varCount_).connection;
        if (connection.isConnected()) {
            connection.disconnect();
            this.bumpNeighbours();
        }
        this.removeInput("VAR" + this.varCount_);

        if (this.varCount_ === this.MIN_COUNT) {
            this.getInput("BUTTONS")
                .removeField("MINUS");
        }
    },
    getIdentifiersFromIntroPattern: function (setWarnings, names) {
        const branchIdentifierList = [];
        for (let i = 0; i < this.varCount_; i++) {
            const block = this.getInputTargetBlock("VAR" + i);
            const branchIdentifiers = block ? block.getIdentifiersFromIntroPattern(setWarnings, [...names, ...branchIdentifierList.flat().flat()]) : [[]];
            branchIdentifierList.push(branchIdentifiers);
        }
        return cartesianProduct(...branchIdentifierList);
    },
    getNumBranches: function () {
        let multiplication = 1;

        for (let i = 0; i < this.varCount_; i++) {
            const block = this.getInputTargetBlock("VAR" + i);
            if (block && block.getNumBranches) {
                const num = block.getNumBranches();
                multiplication *= num;
            }
        }
        return multiplication;
    }
}

Blockly.Blocks['destruct'] = {
    branchCount_: 0,
    MIN_COUNT: 0,

    /**
     * @this {Blockly.Block}
     */
    init: function () {
        this.appendDummyInput()
            .appendField(new Blockly.FieldDropdown([["destruct", "destruct"], ["induction", "induction"]]), "COMMAND")
            .appendField(new Blockly.FieldDropdown([["[Select variable]", "[Select variable]"]]), "VAR")
            .appendField("as");
        this.appendValueInput("PATTERN")
            .setCheck("IntroPattern");
        this.setColour(COLOUR_TACTICS);
        this.setPreviousStatement("Tactic");
        this.setNextStatement("Tactic");
        this.setInputsInline(true);
    },
    mutationToDom: function () {
        const container = varDropdownMutationToDom.call(this);
        container.setAttribute('branchCount', this.branchCount_);
        return container;
    },
    domToMutation: function (xmlElement) {
        varDropdownDomToMutation.call(this, xmlElement);
        const targetCount = parseInt(xmlElement.getAttribute('branchCount'), 10);
        this.updateShape_(targetCount);
    },
    onchange: function (event) {
        /*
        This is to prevent the "Connection lists did not match in length." error. This error occurs when the insertion
        marker (a duplicate of the current block) has a different number of connection compared to the
        current block. Previously, I got such an error I get error when trying to add destruct/induction to the
        Proof block. This is happening because when adding Block A to Block B, insertion markers (Block C) show up,
        which is essentially a greyed out copy of Block A. However, insertion markers do not include any other blocks
        connected to Block A. For example if I'm adding Block A (connected to Blocks E and F) to Block B, the
        insertion marker Block C is only of Block A. For the destruct/induction blocks, the mutation (change in
        shape) relies on the connected IntroPattern block (i.e. when there is no connected IntroPattern block, there
        are 0 statement inputs). Hence, if Block A was having a disjunctive pattern block (2 statement inputs), when
        adding to Block B, the insertion marker Block C has 0 statement inputs, causing the error. This fix checks if
        the current block is an insertion marker (Block C). If it is, it is prevented from updating its shape. Thus,
        it retains the number of branches from the original Block A, causing no error.
         */
        // if (!this.isInsertionMarker_) {
        //     const block = this.getInputTargetBlock("PATTERN");
        //     let targetCount = block?.getNumBranches() ?? 0;
        //     console.log(targetCount);
        //     this.updateShape_(targetCount);
        // }
    },
    updateShape_: function (targetCount) {
        while (this.branchCount_ < targetCount) {
            this.addBranch_();
        }
        while (this.branchCount_ > targetCount) {
            this.removeBranch_();
        }
    },
    addBranch_: function () {
        this.appendStatementInput("STATEMENTS" + this.branchCount_);

        if (this.nextConnection && this.nextConnection.isConnected()) {
            this.nextConnection.disconnect();
            this.bumpNeighbours();
        }
        this.setNextStatement(null);
        this.branchCount_++;
    },
    removeBranch_: function () {
        this.branchCount_--;
        const connection = this.getInput("STATEMENTS" + this.branchCount_).connection;
        if (connection.isConnected()) {
            connection.disconnect();
            this.bumpNeighbours();
        }
        this.removeInput("STATEMENTS" + this.branchCount_);
        this.setNextStatement("Tactic");
    },
    getIdentifiersFromIntroPattern: function (setWarnings, names) {
        const block = this.getInputTargetBlock("PATTERN");
        return block ? block.getIdentifiersFromIntroPattern(setWarnings, names) : [];
    },
    getVarFields: function () {
        return [this.getField("VAR")];
    }
}

Blockly.Blocks['disjunctive_pattern_multiple'] = {
    branchCount_: 2,
    MIN_COUNT: 1,

    init: function () {
        this.appendDummyInput("BUTTONS")
            .appendField(createPlusField(), 'PLUS')
            .appendField(createMinusField(), 'MINUS');
        this.appendDummyInput()
            .appendField("[");
        this.appendValueInput("PATTERN0")
            .setCheck(["IntroPattern", "IntroPatternIdentifier", "MultipleIdentifier"]);
        this.appendValueInput("PATTERN1")
            .setCheck(["IntroPattern", "IntroPatternIdentifier", "MultipleIdentifier"])
            .appendField("|");
        this.appendDummyInput("RIGHT_BRACKET")
            .appendField("]");
        this.setColour(COLOUR_TACTICS);
        this.setOutput(true, ["IntroPattern", "DisjunctionPattern"]);
        this.setInputsInline(true);
    },
    mutationToDom: function () {
        const container = Blockly.utils.xml.createElement('mutation');
        container.setAttribute('branchCount', this.branchCount_);
        return container;
    },
    domToMutation: function (xmlElement) {
        const targetCount = parseInt(xmlElement.getAttribute('branchCount'), 10);
        this.updateShape_(targetCount);
    },
    updateShape_: function (targetCount) {
        while (this.branchCount_ < targetCount) {
            this.addBranch_();
        }
        while (this.branchCount_ > targetCount) {
            this.removeBranch_();
        }
    },
    plus: function () {
        this.addBranch_();
    },
    minus: function () {
        if (this.branchCount_ === this.MIN_COUNT) {
            return;
        }
        this.removeBranch_();
    },
    addBranch_: function () {
        if (this.branchCount_ === this.MIN_COUNT) {
            this.getInput("BUTTONS")
                .appendField(createMinusField(), 'MINUS');
        }
        this.appendValueInput("PATTERN" + this.branchCount_)
            .setCheck(["IntroPattern", "IntroPatternIdentifier", "MultipleIdentifier"])
            .appendField("|");
        this.moveInputBefore("RIGHT_BRACKET", null);
        this.branchCount_++;

    },
    removeBranch_: function () {
        this.branchCount_--;
        const connection = this.getInput("PATTERN" + this.branchCount_).connection;
        if (connection.isConnected()) {
            connection.disconnect();
            this.bumpNeighbours();
        }
        this.removeInput("PATTERN" + this.branchCount_);

        if (this.branchCount_ === this.MIN_COUNT) {
            this.getInput("BUTTONS")
                .removeField("MINUS");
        }
    },
    getNumBranches: function () {
        let count = 0;
        for (let i = 0; i < this.branchCount_; i++) {
            const block = this.getInputTargetBlock("PATTERN" + i);
            if (block && block.getNumBranches && block.getNumBranches() > 0) {
                count += block.getNumBranches();
            } else {
                count++;
            }
        }
        return count;
    },
    getIdentifiersFromIntroPattern: function (setWarnings, names) {
        const identifiers = [];
        for (let i = 0; i < this.branchCount_; i++) {
            const block = this.getInputTargetBlock("PATTERN" + i);
            const branchIdentifiers = block ? block.getIdentifiersFromIntroPattern(setWarnings, [...names, ...identifiers.flat()]) : [[]];
            identifiers.push(...branchIdentifiers);
        }
        return identifiers;
    },
}

Blockly.Blocks['conjunctive_pattern_multiple'] = {
    branchCount_: 2,
    MIN_COUNT: 1,

    init: function () {
        this.appendDummyInput("BUTTONS")
            .appendField(createPlusField(), 'PLUS')
            .appendField(createMinusField(), 'MINUS');
        this.appendDummyInput()
            .appendField("[");
        this.appendValueInput("PATTERN0")
            .setCheck(["IntroPattern", "IntroPatternIdentifier"]);
        this.appendValueInput("PATTERN1")
            .setCheck(["IntroPattern", "IntroPatternIdentifier"]);
        this.appendDummyInput("RIGHT_BRACKET")
            .appendField("]");
        this.setColour(COLOUR_TACTICS);
        this.setOutput(true, "IntroPattern");
        this.setInputsInline(true);
    },
    mutationToDom: function () {
        const container = Blockly.utils.xml.createElement('mutation');
        container.setAttribute('branchCount', this.branchCount_);
        return container;
    },
    domToMutation: function (xmlElement) {
        const targetCount = parseInt(xmlElement.getAttribute('branchCount'), 10);
        this.updateShape_(targetCount);
    },
    updateShape_: function (targetCount) {
        while (this.branchCount_ < targetCount) {
            this.addBranch_();
        }
        while (this.branchCount_ > targetCount) {
            this.removeBranch_();
        }
    },
    plus: function () {
        this.addBranch_();
    },
    minus: function () {
        if (this.branchCount_ === this.MIN_COUNT) {
            return;
        }
        this.removeBranch_();
    },
    addBranch_: function () {
        if (this.branchCount_ === this.MIN_COUNT) {
            this.getInput("BUTTONS")
                .appendField(createMinusField(), 'MINUS');
        }
        this.appendValueInput("PATTERN" + this.branchCount_)
            .setCheck(["IntroPattern", "IntroPatternIdentifier"]);
        this.moveInputBefore("RIGHT_BRACKET", null);
        this.branchCount_++;

    },
    removeBranch_: function () {
        this.branchCount_--;
        const connection = this.getInput("PATTERN" + this.branchCount_).connection;
        if (connection.isConnected()) {
            connection.disconnect();
            this.bumpNeighbours();
        }
        this.removeInput("PATTERN" + this.branchCount_);

        if (this.branchCount_ === this.MIN_COUNT) {
            this.getInput("BUTTONS")
                .removeField("MINUS");
        }
    },
    getIdentifiersFromIntroPattern: function (setWarnings, names) {
        // CARTESIAN PRODUCT
        // [[A]] [[B]] --> [[A, B]]
        // [[A] [B]] [[C] [D]] --> [[A C] [A D] [B C] [B D]]
        // [[A] [B] [C]]  [[D] [E] [F]]  -->  [[A D] [A E] [A F] [B D] [B E] [B F] [C D] [C E] [C F]]
        // [[A] [B]] [[]] --> [[A] [B]]
        // TODO: (A /\ (B \/ C)) \/ (D /\ E)
        const branchIdentifierList = [];
        for (let i = 0; i < this.branchCount_; i++) {
            const block = this.getInputTargetBlock("PATTERN" + i);
            const branchIdentifiers = block ? block.getIdentifiersFromIntroPattern(setWarnings, names) : [[]];
            branchIdentifierList.push(branchIdentifiers);
        }
        return cartesianProduct(...branchIdentifierList);
    },
    getNumBranches: function () {
        let sum = 0;
        let multiplication = 1;

        for (let i = 0; i < this.branchCount_; i++) {
            const block = this.getInputTargetBlock("PATTERN" + i);
            if (block && block.getNumBranches) {
                const num = block.getNumBranches();
                sum += num;
                if (num !== 0) {
                    multiplication *= num;
                }
            }
        }
        if (sum === 0) {
            return 0;
        } else {
            return multiplication;
        }
    }
}


Blockly.Blocks['inductive'] = {
    branchCount_: 2,
    MIN_COUNT: 1,

    /**
     * @this {Blockly.Block}
     */
    init: function () {
        const nameField = new Blockly.FieldTextInput("type_name", variableValidator);
        nameField.setSpellcheck(false);
        nameField.onFinishEditing_ = completeVariableRenaming;

        this.appendDummyInput("BUTTONS")
            .appendField("Inductive")
            .appendField(nameField, "VAR")
            .appendField(":=")
            .appendField(createPlusField(), 'PLUS')
            .appendField(createMinusField(), 'MINUS');
        this.appendDummyInput("NEWLINE0");
        this.appendValueInput("BRANCH0")
            .setCheck("ConstructorDefinition")
            .appendField("|");
        this.appendDummyInput("NEWLINE1")
        this.appendValueInput("BRANCH1")
            .setCheck("ConstructorDefinition")
            .appendField("|");
        this.setColour(COLOUR_COMMANDS);
        this.setInputsInline(true);
    },
    mutationToDom: function () {
        const container = Blockly.utils.xml.createElement('mutation');
        container.setAttribute('branchCount', this.branchCount_);
        return container;
    },
    domToMutation: function (xmlElement) {
        const targetCount = parseInt(xmlElement.getAttribute('branchCount'), 10);
        this.updateShape_(targetCount);
    },
    updateShape_: function (targetCount) {
        while (this.branchCount_ < targetCount) {
            this.addBranch_(false);
        }
        while (this.branchCount_ > targetCount) {
            this.removeBranch_();
        }
    },
    plus: function () {
        this.addBranch_();
    },
    minus: function () {
        if (this.branchCount_ === this.MIN_COUNT) {
            return;
        }
        this.removeBranch_();
    },
    addBranch_: function (shouldAddBlock = true) {
        if (this.branchCount_ === this.MIN_COUNT) {
            this.getInput("BUTTONS")
                .appendField(createMinusField(), 'MINUS');
        }
        this.appendDummyInput("NEWLINE" + this.branchCount_)
        const branchInput = this.appendValueInput("BRANCH" + this.branchCount_)
            .setCheck("ConstructorDefinition")
            .appendField("|");

        if (shouldAddBlock) {
            const block = Blockly.getMainWorkspace().newBlock("constructor_definition");
            block.initSvg();
            block.render();
            block.setName("constructor_name" + this.branchCount_);
            branchInput.connection.connect(block.outputConnection);
        }

        this.branchCount_++;
    },
    removeBranch_: function () {
        this.branchCount_--;
        const constructorBlock = this.getInputTargetBlock("BRANCH" + this.branchCount_);
        if (constructorBlock) {
            constructorBlock.dispose();
        }
        // const connectionCase = this.getInput("BRANCH" + this.branchCount_).connection;
        // if (connectionCase.isConnected()) {
        //     connectionCase.disconnect();
        //     this.bumpNeighbours();
        // }

        this.removeInput("NEWLINE" + this.branchCount_);
        this.removeInput("BRANCH" + this.branchCount_);

        if (this.branchCount_ === this.MIN_COUNT) {
            this.getInput("BUTTONS")
                .removeField("MINUS");
        }
    },
    /**
     * @this {Blockly.Block}
     */
    getConstructorNames: function (setWarnings, allNames) {
        const constructorNames = [];
        for (let i = 0; i < this.branchCount_; i++) {
            const block = this.getInputTargetBlock("BRANCH" + i);
            if (block) {
                const constructorName = block.getFieldValue("VAR");

                if (setWarnings) {
                    if (constructorNames.includes(constructorName) || allNames.includes(constructorName)) {
                        block.setWarningText(`"${constructorName}" has already been defined`);
                    } else {
                        block.setWarningText(null);
                        constructorNames.push(constructorName);
                    }
                } else {
                    if (!block.warning) {
                        constructorNames.push(constructorName);
                    }
                }
            }
        }
        return constructorNames;
    },

    setTypeDropdown: function (options) {
        for (let i = 0; i < this.branchCount_; i++) {
            const block = this.getInputTargetBlock("BRANCH" + i);
            if (block) {
                block.setTypeDropdown(options);
            }
        }
    }
}

Blockly.Blocks['constructor_definition'] = {
    binderCount_: 0,
    MIN_COUNT: 0,

    /**
     * @this {Blockly.Block}
     */
    init: function () {
        const nameField = new Blockly.FieldTextInput("constructor_name", variableValidator);
        nameField.setSpellcheck(false);
        nameField.onFinishEditing_ = completeVariableRenaming;

        this.appendDummyInput("DUMMY")
            .appendField(nameField, "VAR")
            .appendField(createPlusField(), 'PLUS');
        this.setColour(COLOUR_COMMANDS);
        this.setOutput(true, "ConstructorDefinition")
        // this.setInputsInline(true);
        this.setMovable(false);
    },
    mutationToDom: function () {
        const container = Blockly.utils.xml.createElement('mutation');
        container.setAttribute('binderCount', this.binderCount_);
        return container;
    },
    domToMutation: function (xmlElement) {
        const targetCount = parseInt(xmlElement.getAttribute('binderCount'), 10);
        this.updateShape_(targetCount);
    },
    updateShape_: function (targetCount) {
        while (this.binderCount_ < targetCount) {
            this.addBinder_(false);
        }
        while (this.binderCount_ > targetCount) {
            this.removeBinder_();
        }
    },
    plus: function () {
        this.addBinder_();
    },
    minus: function (index) {
        if (this.binderCount_ === this.MIN_COUNT) {
            return;
        }
        this.removeBinder_();
    },
    addBinder_: function (shouldAddBlock = true) {
        let binderInput;
        if (this.binderCount_ === this.MIN_COUNT) {
            const constructorName = this.getFieldValue("VAR");
            this.removeInput('DUMMY');

            const nameField = new Blockly.FieldTextInput(constructorName, variableValidator);
            nameField.setSpellcheck(false);
            nameField.onFinishEditing_ = completeVariableRenaming;
            binderInput = this.appendValueInput("BINDER" + this.binderCount_)
                .setCheck("Binder")
                .appendField(nameField, "VAR")
                .appendField(createPlusField(), 'PLUS')
                .appendField(createMinusField(), 'MINUS');
        } else {
            binderInput = this.appendValueInput('BINDER' + this.binderCount_)
                .setCheck('Binder');
        }

        if (shouldAddBlock) {
            const binderBlock = Blockly.getMainWorkspace().newBlock("binder");
            binderBlock.initSvg();
            binderBlock.render();
            binderInput.connection.connect(binderBlock.outputConnection);
        }

        this.binderCount_++;
    },
    removeBinder_: function () {
        this.binderCount_--;
        const binderBlock = this.getInputTargetBlock("BINDER" + this.binderCount_);
        if (binderBlock) {
            binderBlock.dispose();
        }
        const constructorName = this.getFieldValue("VAR");
        this.removeInput('BINDER' + this.binderCount_);

        if (this.binderCount_ === this.MIN_COUNT) {
            const nameField = new Blockly.FieldTextInput(constructorName, variableValidator);
            nameField.setSpellcheck(false);
            nameField.onFinishEditing_ = completeVariableRenaming;
            this.appendDummyInput("DUMMY")
                .appendField(nameField, "VAR")
                .appendField(createPlusField(), 'PLUS');
        }

        this.bumpNeighbours();
    },
    setTypeDropdown: function (options) {
        for (let i = 0; i < this.binderCount_; i++) {
            const block = this.getInputTargetBlock("BINDER" + i);
            if (block) {
                block.setTypeDropdown(options);
            }
        }
    },
    getIdentifiers: function (setWarnings, names) {
        const identifiers = [];
        const newTypes = [];
        for (let i = 0; i < this.binderCount_; i++) {
            const binderBlock = this.getInputTargetBlock("BINDER" + i);
            if (binderBlock) {
                binderBlock.addTypeDropdown(newTypes.map(value => [value, value]));

                const [binderIdentifiers, binderNewTypes] = binderBlock.getIdentifiers();
                if (setWarnings) {
                    const uniqueIdentifiers = new Set(binderIdentifiers);
                    const selectedTypes = []
                    for (let j = 0; j < binderBlock.typeCount_; j++) {
                        const selectedType = binderBlock.getFieldValue("TYPE" + j);
                        selectedTypes.push(selectedType);
                    }
                    const warnings = new Set();

                    if (selectedTypes.some(selectedType => !names.includes(selectedType))) {
                        warnings.add("Please ensure the selected type has been defined.")
                    }

                    if (uniqueIdentifiers.size !== binderIdentifiers.length
                        || binderIdentifiers.some(identifier => identifiers.includes(identifier) || names.includes(identifier))) {
                        warnings.add("Duplicate variable names.");
                    }

                    if (warnings.size === 0) {
                        binderBlock.setWarningText(null);
                    } else {
                        binderBlock.setWarningText([...warnings].join("\n"));
                    }
                }
                const typesToAdd = binderNewTypes.filter(type => !names.includes(type) && !newTypes.includes(type));
                newTypes.push(...typesToAdd);
                identifiers.push(...binderIdentifiers);
            }
        }
        const filteredIdentifiers = [...new Set(identifiers)].filter(identifier => !names.includes(identifier)); // Sets in JavaScript maintain insertion order
        return [filteredIdentifiers, newTypes];
    },
    setName: function (name) {
        this.getField("VAR").setValue(name);
    }
}


// TODO: what to allow in the case portion?

// Constructor + no argument (e.g. O, monday)

// Constructor + argument specified (e.g. primary red, S O) (Nested constructors)

// Constructor + argument variable (e.g. S n')
// Constructor + underscore (e.g. S _)

// Underscore (e.g. _)

Blockly.Blocks['match'] = {
    branchCount_: 2,
    MIN_COUNT: 1,

    /**
     * @this {Blockly.Block}
     */
    init: function () {
        this.appendDummyInput("BUTTONS")
            .appendField("match")
            .appendField(new Blockly.FieldDropdown([["[Select variable]", "[Select variable]"]]), "VAR")
            .appendField("with")
            .appendField(createPlusField(), 'PLUS')
            .appendField(createMinusField(), 'MINUS');
        this.appendDummyInput("NEWLINE0");
        this.appendValueInput("CASE0")
            .setCheck("CaseConstructor")
            .appendField("|");
        this.appendValueInput("RESULT0")
            .setCheck("Expression")
            .appendField("=>");
        this.appendDummyInput("NEWLINE1");
        this.appendValueInput("CASE1")
            .setCheck("CaseConstructor")
            .appendField("|");
        this.appendValueInput("RESULT1")
            .setCheck("Expression")
            .appendField("=>");
        this.setColour(COLOUR_EXPRESSIONS);
        this.setOutput(true, "Expression");
        this.setInputsInline(true);
    },
    mutationToDom: function () {
        const container = varDropdownMutationToDom.call(this);
        container.setAttribute('branchCount', this.branchCount_);
        return container;
    },
    domToMutation: function (xmlElement) {
        varDropdownDomToMutation.call(this, xmlElement);
        const targetCount = parseInt(xmlElement.getAttribute('branchCount'), 10);
        this.updateShape_(targetCount);
    },
    updateShape_: function (targetCount) {
        while (this.branchCount_ < targetCount) {
            this.addBranch_(false);
        }
        while (this.branchCount_ > targetCount) {
            this.removeBranch_();
        }
    },
    plus: function () {
        this.addBranch_();
    },
    minus: function () {
        if (this.branchCount_ === this.MIN_COUNT) {
            return;
        }
        this.removeBranch_();
    },
    addBranch_: function (shouldAddBlock = true) {
        if (this.branchCount_ === this.MIN_COUNT) {
            this.getInput("BUTTONS")
                .appendField(createMinusField(), 'MINUS');
        }
        this.appendDummyInput("NEWLINE" + this.branchCount_);
        const caseInput = this.appendValueInput("CASE" + this.branchCount_)
            .setCheck("CaseConstructor")
            .appendField("|");
        this.appendValueInput("RESULT" + this.branchCount_)
            .setCheck("Expression")
            .appendField("=>");

        if (shouldAddBlock) {
            const block = Blockly.getMainWorkspace().newBlock("case_constructor");
            block.initSvg();
            block.render();
            caseInput.connection.connect(block.outputConnection);
        }

        this.branchCount_++;
    },
    removeBranch_: function () {
        this.branchCount_--;
        this.getInputTargetBlock("CASE" + this.branchCount_)?.dispose();
        this.getInputTargetBlock("RESULT" + this.branchCount_)?.dispose();

        // const connectionCase = this.getInput("CASE" + this.branchCount_).connection;
        // if (connectionCase.isConnected()) {
        //     connectionCase.disconnect();
        //     this.bumpNeighbours();
        // }
        // const connectionResult = this.getInput("RESULT" + this.branchCount_).connection;
        // if (connectionResult.isConnected()) {
        //     connectionResult.disconnect();
        //     this.bumpNeighbours();
        // }

        this.removeInput("NEWLINE" + this.branchCount_);
        this.removeInput("CASE" + this.branchCount_);
        this.removeInput("RESULT" + this.branchCount_);

        if (this.branchCount_ === this.MIN_COUNT) {
            this.getInput("BUTTONS")
                .removeField("MINUS");
        }
    },
    getVarFields: function () {
        return [this.getField("VAR")];
    },
    getCaseConstrBlocks: function () {
        const blocks = [];
        for (let i = 0; i < this.branchCount_; i++) {
            const caseBlock = this.getInputTargetBlock("CASE" + i);
            if (caseBlock) {
                blocks.push(...caseBlock.getCaseConstrBlocks());
            }
        }
        return blocks;
    }
}


Blockly.Blocks['definition_or_fixpoint'] = {
    binderCount_: 1,
    MIN_COUNT: 0,

    /**
     * @this {Blockly.Block}
     */
    init: function () {
        const nameField = new Blockly.FieldTextInput("definition_name", variableValidator);
        nameField.setSpellcheck(false);
        nameField.onFinishEditing_ = completeVariableRenaming;

        this.appendValueInput("BINDER0")
            .setCheck("Binder")
            .appendField(new Blockly.FieldDropdown([["Definition", "Definition"], ["Fixpoint", "Fixpoint"]]), "COMMAND")
            .appendField(nameField, "VAR")
            .appendField(createPlusField(), 'PLUS')
            .appendField(createMinusField(), 'MINUS');
        this.appendValueInput("EXPRESSION")
            .setCheck(["Expression", "Proposition"])
            .appendField(":")
            .appendField(new Blockly.FieldDropdown([
                ["Prop", "Prop"],
                ["nat", "nat"],
                ["bool", "bool"],
                ["Type", "Type"]
            ]), "TYPE")
            .appendField(":=")
            .setAlign(Blockly.ALIGN_RIGHT);
        this.setColour(COLOUR_COMMANDS);
        // this.setInputsInline(true);
    },

    /**
     * Creates XML to represent the number of inputs.
     * @return {Element} XML storage element.
     * @this {Blockly.Block}
     */
    mutationToDom: function () {
        const container = Blockly.utils.xml.createElement('mutation');
        container.setAttribute('binderCount', this.binderCount_);
        const options = this.getField("TYPE").getOptions(false);
        container.setAttribute('options', JSON.stringify(options));
        return container;
    },

    /**
     * Parses XML to restore the inputs.
     * @param {!Element} xmlElement XML storage element.
     * @this {Blockly.Block}
     */
    domToMutation: function (xmlElement) {
        const targetCount = parseInt(xmlElement.getAttribute('binderCount'), 10);
        const options = xmlElement.getAttribute('options');
        const parsedOptions = JSON.parse(options);
        if (parsedOptions) {
            this.getField("TYPE").menuGenerator_ = parsedOptions;
        }
        this.updateShape_(targetCount);
    },

    /**
     * Adds inputs to the block until the block matches the target count.
     * @param {number} targetCount The target number of inputs.
     * @this {Blockly.Block}
     * @private
     */
    updateShape_: function (targetCount) {
        while (this.binderCount_ < targetCount) {
            this.addBinder_(false);
        }
        while (this.binderCount_ > targetCount) {
            this.removeBinder_();
        }
    },

    /**
     * Callback for the plus field. Adds an input to the block.
     */
    plus: function () {
        this.addBinder_();
    },

    /**
     * Callback for the minus field. Triggers "removing" the input at the specific
     * index.
     * @see removeInput_
     * @param {number} index The index of the input to "remove".
     * @this {Blockly.Block}
     */
    minus: function (index) {
        if (this.binderCount_ === this.MIN_COUNT) {
            return;
        }
        this.removeBinder_();
    },

    /**
     * Adds an input to the bottom of the block.
     * @this {Blockly.Block}
     * @private
     */
    addBinder_: function (shouldAddBlock = true) {
        let binderInput;
        if (this.binderCount_ === this.MIN_COUNT) {
            const commandName = this.getFieldValue("COMMAND");
            const definitionName = this.getFieldValue("VAR");
            this.removeInput('DUMMY');

            const nameField = new Blockly.FieldTextInput(definitionName, variableValidator);
            nameField.setSpellcheck(false);
            nameField.onFinishEditing_ = completeVariableRenaming;

            const commandField = new Blockly.FieldDropdown([["Definition", "Definition"], ["Fixpoint", "Fixpoint"]]);
            commandField.setValue(commandName);

            binderInput = this.appendValueInput("BINDER" + this.binderCount_)
                .setCheck("Binder")
                .appendField(commandField, "COMMAND")
                .appendField(nameField, "VAR")
                .appendField(createPlusField(), 'PLUS')
                .appendField(createMinusField(), 'MINUS');
        } else {
            binderInput = this.appendValueInput('BINDER' + this.binderCount_)
                .setCheck('Binder');
        }
        this.moveInputBefore("EXPRESSION", null);

        if (shouldAddBlock) {
            const binderBlock = Blockly.getMainWorkspace().newBlock("binder");
            binderBlock.initSvg();
            binderBlock.render();
            binderInput.connection.connect(binderBlock.outputConnection);
        }

        this.binderCount_++;
    },

    /**
     * Appears to remove the input at the given index. Actually shifts attached
     * blocks and then removes the input at the bottom of the block. This is to
     * make sure the inputs are always BINDER0, BINDER1, etc. with no gaps.
     * @this {Blockly.Block}
     * @private
     */
    removeBinder_: function () {
        this.binderCount_--;
        const binderBlock = this.getInputTargetBlock("BINDER" + this.binderCount_);
        if (binderBlock) {
            binderBlock.dispose();
        }
        const commandName = this.getFieldValue("COMMAND");
        const definitionName = this.getFieldValue("VAR");
        this.removeInput('BINDER' + this.binderCount_);

        if (this.binderCount_ === this.MIN_COUNT) {
            const nameField = new Blockly.FieldTextInput(definitionName, variableValidator);
            nameField.setSpellcheck(false);
            nameField.onFinishEditing_ = completeVariableRenaming;
            const commandField = new Blockly.FieldDropdown([["Definition", "Definition"], ["Fixpoint", "Fixpoint"]]);
            commandField.setValue(commandName);
            this.appendDummyInput("DUMMY")
                .appendField(commandField, "COMMAND")
                .appendField(nameField, "VAR")
                .appendField(createPlusField(), 'PLUS');
            this.moveInputBefore("EXPRESSION", null);
        }

        this.bumpNeighbours();
    },

    getIdentifiers: function (setWarnings, names) {
        const identifiers = [];
        const newTypes = [];
        for (let i = 0; i < this.binderCount_; i++) {
            const binderInput = this.getInput("BINDER" + i);
            if (binderInput.connection.isConnected()) {
                const binderBlock = binderInput.connection.targetBlock();
                binderBlock.addTypeDropdown(newTypes.map(value => [value, value]));

                const [binderIdentifiers, binderNewTypes] = binderBlock.getIdentifiers();
                if (setWarnings) {
                    const uniqueIdentifiers = new Set(binderIdentifiers);
                    const selectedTypes = []
                    for (let j = 0; j < binderBlock.typeCount_; j++) {
                        const selectedType = binderBlock.getFieldValue("TYPE" + j);
                        selectedTypes.push(selectedType);
                    }
                    const warnings = new Set();

                    if (selectedTypes.some(selectedType => !names.includes(selectedType))) {
                        warnings.add("Please ensure the selected type has been defined.")
                    }

                    if (uniqueIdentifiers.size !== binderIdentifiers.length
                        || binderIdentifiers.some(identifier => identifiers.includes(identifier) || names.includes(identifier))) {
                        warnings.add("Duplicate variable names.");
                    }

                    if (warnings.size === 0) {
                        binderBlock.setWarningText(null);
                    } else {
                        binderBlock.setWarningText([...warnings].join("\n"));
                    }
                }
                const typesToAdd = binderNewTypes.filter(type => !names.includes(type) && !newTypes.includes(type));
                newTypes.push(...typesToAdd);
                identifiers.push(...binderIdentifiers);
            }
        }
        const filteredIdentifiers = [...new Set(identifiers)].filter(identifier => !names.includes(identifier)); // Sets in JavaScript maintain insertion order
        return [filteredIdentifiers, newTypes];
    },
    setTypeDropdown: function (options) {
        const field = this.getField("TYPE");
        field.menuGenerator_ = options;
        for (let i = 0; i < this.binderCount_; i++) {
            const block = this.getInputTargetBlock("BINDER" + i);
            if (block) {
                block.setTypeDropdown(options);
            }
        }
    },
    getTypeFields: function () {
        return [this.getField("TYPE")];
    }
}

Blockly.Blocks['theorem'] = {
    /**
     * @this {Blockly.Block}
     */
    init: function () {
        const nameField = new Blockly.FieldTextInput("theorem_name", variableValidator);
        nameField.setSpellcheck(false);
        nameField.onFinishEditing_ = completeVariableRenaming;
        this.appendDummyInput()
            .appendField("Theorem")
            .appendField(nameField, "VAR");
        this.appendDummyInput("NEWLINE");
        this.appendValueInput("PROPOSITION")
            .setCheck("Proposition");
        this.setNextStatement("Proof");
        this.setColour(COLOUR_COMMANDS);
        this.setInputsInline(true);
    },
}

Blockly.Blocks['variable_dropdown_multiple'] = {
    extraVarCount_: 1,
    MIN_COUNT: 1,

    init: function () {
        this.appendDummyInput("BUTTONS")
            .appendField("(")
            .appendField(createPlusField(), 'PLUS');
        this.appendDummyInput("VARS")
            .appendField(new Blockly.FieldDropdown([["[Select variable]", "[Select variable]"]]), "VAR");
        this.appendValueInput("VAR0")
            .setCheck(["VarExpression", "Nat", "Bool"]);
        this.appendDummyInput("RIGHT_BRACKET")
            .appendField(")");
        this.setColour(COLOUR_VAR);
        this.setOutput(true, ["Proposition", "Expression", "Nat", "Bool", "VarExpression"]);
        this.setInputsInline(true);
    },

    mutationToDom: function () {
        const container = Blockly.utils.xml.createElement('mutation');
        container.setAttribute('extraVarCount', this.extraVarCount_);
        const options = this.getField("VAR").getOptions(false);
        container.setAttribute('options', JSON.stringify(options));
        return container;
    },
    domToMutation: function (xmlElement) {
        const targetCount = parseInt(xmlElement.getAttribute('extraVarCount'), 10);
        this.updateShape_(targetCount, false);
        const options = xmlElement.getAttribute('options');
        const parsedOptions = JSON.parse(options);
        if (parsedOptions) {
            this.getField("VAR").menuGenerator_ = parsedOptions;
        }
    },
    updateShape_: function (targetCount, shouldAddBlock = true) {
        while (this.extraVarCount_ < targetCount) {
            this.addVar_(shouldAddBlock);
        }
        while (this.extraVarCount_ > targetCount) {
            this.removeVar_();
        }
    },
    plus: function () {
        this.addVar_();
    },
    minus: function () {
        if (this.extraVarCount_ === this.MIN_COUNT) {
            return;
        }
        this.removeVar_();
    },
    addVar_: function (shouldAddBlock = true) {
        if (this.extraVarCount_ === this.MIN_COUNT) {
            this.getInput("BUTTONS")
                .appendField(createMinusField(), 'MINUS');
        }
        const varInput = this.appendValueInput("VAR" + this.extraVarCount_)
            .setCheck(["VarExpression", "Nat", "Bool"]);

        if (shouldAddBlock) {
            const block = Blockly.getMainWorkspace().newBlock("variable_dropdown");
            block.initSvg();
            block.render();
            varInput.connection.connect(block.outputConnection);
        }

        this.moveInputBefore("RIGHT_BRACKET", null);
        this.extraVarCount_++;

    },
    removeVar_: function () {
        this.extraVarCount_--;
        this.getInputTargetBlock("VAR" + this.extraVarCount_)?.dispose();
        this.removeInput("VAR" + this.extraVarCount_);

        if (this.extraVarCount_ === this.MIN_COUNT) {
            this.getInput("BUTTONS")
                .removeField("MINUS");
        }
    },
    getVarFields: function () {
        const varFields = [this.getField("VAR")];
        for (let i = 0; i < this.extraVarCount_; i++) {
            const block = this.getInputTargetBlock("VAR" + this.extraVarCount_);
            if (block) {
                varFields.push(...block.getVarFields());
            }
        }
        return varFields;
    }
    // getIdentifiers: function () {
    //     const identifiers = [];
    //     for (let i = 0; i < this.extraVarCount_; i++) {
    //         const block = this.getInputTargetBlock("VAR" + i);
    //         if (block) {
    //             console.assert(block.type === "intro_pattern_identifier");
    //             const blockIdentifiers = block.getIdentifiers();
    //             console.assert(blockIdentifiers.length === 1);
    //             console.assert(blockIdentifiers[0].length === 1);
    //             identifiers.push(blockIdentifiers[0][0]);
    //         }
    //     }
    //     return [identifiers];
    // }
}


Blockly.Blocks['case_identifier'] = {
    init: function () {
        const nameField = new Blockly.FieldTextInput("var_name", variableValidator);
        nameField.setSpellcheck(false);
        // HACK to make sure that traversal is done only after text field has been edited completely.
        // Don't traverse during intermediate states.
        // See https://github.com/google/blockly/issues/4350
        nameField.onFinishEditing_ = completeVariableRenaming;

        this.setColour(COLOUR_EXPRESSIONS);
        this.setOutput(true, "CaseIdentifier");

        this.appendDummyInput()
            .appendField(nameField, 'VAR');
    },
    getIdentifiers: function (setWarnings, names) {
        const identifier = this.getFieldValue("VAR");
        if (names.includes(identifier)) {
            this.setWarningText(`"${identifier}" has already been defined.`);
            return [];
        } else {
            this.setWarningText(null);
            return [identifier];
        }
    },
    getCaseConstrBlocks: function () {
        return [];
    }
};

Blockly.Blocks['case_constructor'] = {
    argCount_: 0,
    MIN_COUNT: 0,

    init: function () {
        this.appendDummyInput("DUMMY")
            .appendField(new Blockly.FieldDropdown([["[Select constructor]", "[Select constructor]"]]), "VAR")
        this.setColour(COLOUR_EXPRESSIONS);
        this.setOutput(true, "CaseConstructor");
        this.setInputsInline(true);
    },

    mutationToDom: function () {
        const container = varDropdownMutationToDom.call(this);
        container.setAttribute('argCount', this.argCount_);
        return container;
    },
    domToMutation: function (xmlElement) {
        varDropdownDomToMutation.call(this, xmlElement);
        const targetCount = parseInt(xmlElement.getAttribute('argCount'), 10);
        this.updateShape_(targetCount, false);
    },
    updateShape_: function (targetCount, shouldAddBlock = true) {
        while (this.argCount_ < targetCount) {
            this.addArg_(shouldAddBlock);
        }
        while (this.argCount_ > targetCount) {
            this.removeArg_();
        }
    },
    addArg_: function (shouldAddBlock = true) {
        const argInput = this.appendValueInput("ARG" + this.argCount_)
            .setCheck(["CaseConstructor", "CaseIdentifier"]);

        this.argCount_++;

        if (shouldAddBlock) {
            const block = Blockly.getMainWorkspace().newBlock("case_identifier");
            block.initSvg();
            block.render();
            argInput.connection.connect(block.outputConnection);
        }
    },
    removeArg_: function () {
        this.argCount_--;
        this.getInputTargetBlock("ARG" + this.argCount_)?.dispose();
        this.removeInput("ARG" + this.argCount_);
        this.bumpNeighbours();
    },
    getCaseConstrBlocks: function () {
        const blocks = [this];
        for (let i = 0; i < this.argCount_; i++) {
            const argBlock = this.getInputTargetBlock("ARG" + i);
            if (argBlock) {
                blocks.push(...argBlock.getCaseConstrBlocks());
            }
        }
        return blocks;
    },
    getIdentifiers: function (setWarnings, names) {
        const identifiers = [];
        for (let i = 0; i < this.argCount_; i++) {
            const argBlock = this.getInputTargetBlock("ARG" + i);
            if (argBlock) {
                identifiers.push(...argBlock.getIdentifiers(setWarnings, [...names, ...identifiers]));
            }
        }
        return identifiers;
    },
    getVarFields: function () {
        return [this.getField("VAR")];
    }
    // getIdentifiers: function () {
    //     const identifiers = [];
    //     for (let i = 0; i < this.varCount_; i++) {
    //         const block = this.getInputTargetBlock("VAR" + i);
    //         if (block) {
    //             console.assert(block.type === "intro_pattern_identifier");
    //             const blockIdentifiers = block.getIdentifiers();
    //             console.assert(blockIdentifiers.length === 1);
    //             console.assert(blockIdentifiers[0].length === 1);
    //             identifiers.push(blockIdentifiers[0][0]);
    //         }
    //     }
    //     return [identifiers];
    // }
}