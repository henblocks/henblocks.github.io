Blockly.defineBlocksWithJsonArray([
    {
        "type": "proof",
        "message0": "Proof",
        "message1": "%1",
        "args1": [
            {
                "type": "input_statement",
                "name": "STATEMENTS"
            },
        ],
        "previousStatement": ["Proof"],
        "colour": COLOUR_COMMANDS,
    },
    {
        "type": "reflexivity",
        "message0": "reflexivity",
        "previousStatement": "Tactic",
        "nextStatement": "Tactic",
        "colour": COLOUR_TACTICS,
    },
    {
        "type": "simpl",
        "message0": "simpl",
        "previousStatement": "Tactic",
        "nextStatement": "Tactic",
        "colour": COLOUR_TACTICS,
    },
    {
        "type": "left_right",
        "message0": "%1",
        "args0": [
            {
                "type": "field_dropdown",
                "name": "COMMAND",
                "options": [
                    ["left", "left"],
                    ["right", "right"],
                ]
            },
        ],
        "previousStatement": "Tactic",
        "nextStatement": "Tactic",
        "colour": COLOUR_TACTICS,
    },
    // {
    //     "type": "right",
    //     "message0": "right",
    //     "previousStatement": "Tactic",
    //     "nextStatement": "Tactic",
    //     "colour": COLOUR_TACTICS,
    // },
    {
        "type": "symmetry",
        "message0": "symmetry",
        "previousStatement": "Tactic",
        "nextStatement": "Tactic",
        "colour": COLOUR_TACTICS,
    },
    {
        "type": "f_equal",
        "message0": "f_equal",
        "previousStatement": "Tactic",
        "nextStatement": "Tactic",
        "colour": COLOUR_TACTICS,
    },
    {
        "type": "split",
        "message0": "split %1",
        "args0": [
            {
                "type": "input_statement",
                "name": "STATEMENTS_LEFT"
            },
        ],
        "message1": "%1",
        "args1": [
            {
                "type": "input_statement",
                "name": "STATEMENTS_RIGHT"
            },
        ],
        "previousStatement": "Tactic",
        "colour": COLOUR_TACTICS,
    },
    {
        "type": "exact",
        "message0": "exact %1",
        "args0": [
            // {
            //     "type": "field_dropdown",
            //     "name": "HYPOTHESIS",
            //     "options": [
            //         ["[Select variable]", "[Select variable]"],
            //     ]
            // },
            {
                "type": "input_value",
                "name": "VAR",
                "check": "VarExpression",
            }
        ],
        "previousStatement": "Tactic",
        "nextStatement": "Tactic",
        "colour": COLOUR_TACTICS,
    },
    {
        "type": "revert",
        "message0": "revert %1",
        "args0": [
            {
                "type": "field_variable",
                "name": "VAR",
                "variable": "item",
                "variableTypes": [""]
            },
        ],
        "previousStatement": "Tactic",
        "nextStatement": "Tactic",
        "colour": COLOUR_TACTICS,
    },
    {
        "type": "rewrite",
        "message0": "rewrite %1 %2",
        "args0": [
            {
                "type": "field_dropdown",
                "name": "ARROW",
                "options": [
                    ["➝", "LTR"],
                    ["←", "RTL"]
                ]
            },
            {
                "type": "input_value",
                "name": "VAR",
                "check": "VarExpression",
            },
        ],
        "previousStatement": "Tactic",
        "nextStatement": "Tactic",
        "colour": COLOUR_TACTICS,
    },
    {
        "type": "unfold",
        "message0": "unfold %1",
        "args0": [
            {
                "type": "field_variable",
                "name": "VAR",
                "variable": "item",
                "variableTypes": [""]
            },
        ],
        "previousStatement": "Tactic",
        "nextStatement": "Tactic",
        "colour": COLOUR_TACTICS,
    },
    {
        "type": "conjunctive_pattern",
        "message0": "[%1 %2]",
        "args0": [
            {
                "type": "input_value",
                "name": "LEFT",
                "check": ["IntroPattern", "IntroPatternIdentifier"],
            },
            {
                "type": "input_value",
                "name": "RIGHT",
                "check": ["IntroPattern", "IntroPatternIdentifier"],
            },
        ],
        "colour": COLOUR_TACTICS,
        "inputsInline": true,
        "output": "IntroPattern",
    },
    {
        "type": "disjunctive_pattern",
        "message0": "[%1 | %2]",
        "args0": [
            {
                "type": "input_value",
                "name": "LEFT",
                "check": ["IntroPattern", "IntroPatternIdentifier", "MultipleIdentifier"],
            },
            {
                "type": "input_value",
                "name": "RIGHT",
                "check": ["IntroPattern", "IntroPatternIdentifier", "MultipleIdentifier"],
            },
        ],
        "colour": COLOUR_TACTICS,
        "inputsInline": true,
        "output": ["IntroPattern", "DisjunctionPattern"],
    },
    // {
    //     "type": "refine",
    //     "message0": "refine %1",
    //     "args0": [
    //         {
    //             "type": "input_value",
    //             "name": "VALUE"
    //         },
    //     ],
    //     "previousStatement": "Tactic",
    //     "nextStatement": "Tactic",
    //     "colour": COLOUR_TACTICS,
    // },
    // {
    //     "type": "function_application",
    //     "message0": "%1 %2",
    //     "args0": [
    //         {
    //             "type": "field_variable",
    //             "name": "FUN",
    //             "variable": "function",
    //             "variableTypes": [""]
    //         },
    //         {
    //             "type": "field_variable",
    //             "name": "ARG",
    //             "variable": "argument",
    //             "variableTypes": [""]
    //         },
    //     ],
    //     "output": null,
    //     "colour": COLOUR_VAR,
    // },
    // {
    //     "type": "match",
    //     "message0": "match %1 with",
    //     "args0": [
    //         {
    //             "type": "field_variable",
    //             "name": "VAR1",
    //             "variable": "variable",
    //             "variableTypes": [""]
    //         },
    //     ],
    //     "message1": "| %1 => %2",
    //     "args1": [
    //         {
    //             "type": "field_input",
    //             "name": "CASE1",
    //             "text": "case",
    //             "spellcheck": false
    //         },
    //         {
    //             "type": "field_input",
    //             "name": "RESULT1",
    //             "text": "result",
    //             "spellcheck": false
    //         },
    //     ],
    //     "message2": "end",
    //     "output": null,
    //     "colour": COLOUR_PROPOSITIONS,
    // },
    {
        "type": "variable_dropdown",
        "message0": "%1",
        "args0": [
            {
                "type": "field_dropdown",
                "name": "VAR",
                "options": [
                    ["[Select variable]", "[Select variable]"],
                ]
            },
        ],
        "output": ["Proposition", "Expression", "Nat", "Bool", "VarExpression"],
        "colour": COLOUR_VAR,
    },
    {
        "type": "variable",
        "message0": "%1",
        "args0": [
            {
                "type": "field_variable",
                "name": "VAR",
                "variable": "item",
                "variableTypes": [""]
            },
        ],
        "output": null,
        "colour": COLOUR_VAR,
    },
    {
        "type": "equality",
        "message0": "%1 = %2",
        "args0": [
            {
                "type": "input_value",
                "name": "LEFT",
                "check": ["Expression", "Nat"],
            },
            {
                "type": "input_value",
                "name": "RIGHT",
                "check": ["Expression", "Nat"],
            },
        ],
        "colour": COLOUR_PROPOSITIONS,
        "inputsInline": true,
        "output": "Proposition",
    },
    {
        "type": "true_or_false_proposition",
        "message0": "%1",
        "args0": [
            {
                "type": "field_dropdown",
                "name": "BOOL",
                "options": [
                    ["True", "True"],
                    ["False", "False"],
                ]
            },
        ],
        "colour": COLOUR_PROPOSITIONS,
        "output": ["Proposition"],
    },
    {
        "type": "true_or_false_expression",
        "message0": "%1",
        "args0": [
            {
                "type": "field_dropdown",
                "name": "BOOL",
                "options": [
                    ["true", "true"],
                    ["false", "false"],
                ]
            },
        ],
        "colour": COLOUR_EXPRESSIONS,
        "output": ["Expression"],
    },
    {
        "type": "not",
        "message0": "~%1",
        "args0": [
            {
                "type": "input_value",
                "name": "PROPOSITION",
                "check": "Proposition",
            },
        ],
        "colour": COLOUR_PROPOSITIONS,
        // "inputsInline": true,
        "output": "Proposition",
    },
    {
        "type": "implies",
        "message0": "%1 ➝ %2",
        "args0": [
            {
                "type": "input_value",
                "name": "LEFT",
                "check": "Proposition",
            },
            {
                "type": "input_value",
                "name": "RIGHT",
                "check": "Proposition",
            },
        ],
        "colour": COLOUR_PROPOSITIONS,
        "inputsInline": true,
        "output": "Proposition",
    },
    {
        "type": "conjunction_disjunction",
        "message0": "%1 %2 %3",
        "args0": [
            {
                "type": "input_value",
                "name": "LEFT",
                "check": "Proposition",
            },
            {
                "type": "field_dropdown",
                "name": "OPERATOR",
                "options": [
                    ["∧", "/\\"],
                    ["∨", "\\/"],
                ]
            },
            {
                "type": "input_value",
                "name": "RIGHT",
                "check": "Proposition",
            },
        ],
        "colour": COLOUR_PROPOSITIONS,
        "inputsInline": true,
        "output": "Proposition",
    },
    // {
    //     "type": "conjunction",
    //     "message0": "%1 ∧ %2",
    //     "args0": [
    //         {
    //             "type": "input_value",
    //             "name": "LEFT",
    //             "check": "Proposition",
    //         },
    //         {
    //             "type": "input_value",
    //             "name": "RIGHT",
    //             "check": "Proposition",
    //         },
    //     ],
    //     "colour": COLOUR_PROPOSITIONS,
    //     "inputsInline": true,
    //     "output": "Proposition",
    // },
    // {
    //     "type": "disjunction",
    //     "message0": "%1 ∨ %2",
    //     "args0": [
    //         {
    //             "type": "input_value",
    //             "name": "LEFT",
    //             "check": "Proposition",
    //         },
    //         {
    //             "type": "input_value",
    //             "name": "RIGHT",
    //             "check": "Proposition",
    //         },
    //     ],
    //     "colour": COLOUR_PROPOSITIONS,
    //     "inputsInline": true,
    //     "output": null,
    // },
    {
        "type": "forall",
        "message0": "%1 %2",
        "args0": [
            {
                "type": "field_dropdown",
                "name": "COMMAND",
                "options": [
                    ["forall", "forall"],
                    ["exists", "exists"],
                ]
            },
            {
                "type": "input_value",
                "name": "BINDER0",
                "check": "Binder",
            },
        ],
        "message1": ",%1",
        "args1": [
            {
                "type": "input_value",
                "name": "PROPOSITION",
                "check": "Proposition",
                "align": "RIGHT",
            },
        ],
        "colour": COLOUR_PROPOSITIONS,
        "output": "Proposition",
        "mutator": "forall_exists_mutator",
    },
    {
        "type": "exists",
        "message0": "exists %1",
        "args0": [
            {
                "type": "input_value",
                "name": "BINDER0",
                "check": "Binder",
            },
        ],
        "message1": ",%1",
        "args1": [
            {
                "type": "input_value",
                "name": "PROPOSITION",
                "check": "Proposition",
                "align": "RIGHT",
            },
        ],
        "colour": COLOUR_PROPOSITIONS,
        "output": "Proposition",
        "mutator": "forall_exists_mutator",
    },
    {
        "type": "binder_dialog",
        "message0": "%1 : %2",
        "args0": [
            {
                "type": "field_input",
                "name": "VAR0",
                "text": "var0",
                "spellcheck": false
            },
            {
                "type": "field_dropdown",
                "name": "TYPES",
                "options": [
                    ["Prop", "Prop"],
                    ["nat", "nat"],
                    ["bool", "bool"],
                    ["Type", "Type"],
                ],
            },
        ],
        "colour": COLOUR_VAR,
        "output": "Binder",
        "mutator": "binder_dialog_mutator",
    },
    {
        "type": "binder_dialog_container",
        "message0": "Number of variables: %1",
        "args0": [
            {
                "type": "input_statement",
                "name": "STACK"
            },
        ],
        "enableContextMenu": false,
        "colour": COLOUR_VAR,
    },
    {
        "type": "binder_dialog_var",
        "message0": "Variable",
        "previousStatement": null,
        "nextStatement": null,
        "enableContextMenu": false,
        "colour": COLOUR_VAR,
        "tooltip": "Add a variable to the binder block"
    },
    {
        "type": "math_operation",
        "message0": "%1 %2 %3",
        "args0": [
            {
                "type": "input_value",
                "name": "LEFT",
                "check": "Nat",
            },
            {
                "type": "field_dropdown",
                "name": "OPERATOR",
                "options": [
                    ["+", "+"],
                    ["x", "*"],
                ]
            },
            {
                "type": "input_value",
                "name": "RIGHT",
                "check": "Nat",
            },
        ],
        "colour": COLOUR_EXPRESSIONS,
        "inputsInline": true,
        "output": "Nat",
    },
    // {
    //     "type": "addition",
    //     "message0": "%1 + %2",
    //     "args0": [
    //         {
    //             "type": "input_value",
    //             "name": "LEFT",
    //             "check": "Nat",
    //         },
    //         {
    //             "type": "input_value",
    //             "name": "RIGHT",
    //             "check": "Nat",
    //         },
    //     ],
    //     "colour": COLOUR_PROPOSITIONS,
    //     "inputsInline": true,
    //     "output": "Nat",
    // },
    // {
    //     "type": "multiplication",
    //     "message0": "%1 x %2",
    //     "args0": [
    //         {
    //             "type": "input_value",
    //             "name": "LEFT",
    //             "check": "Nat",
    //         },
    //         {
    //             "type": "input_value",
    //             "name": "RIGHT",
    //             "check": "Nat",
    //         },
    //     ],
    //     "colour": COLOUR_PROPOSITIONS,
    //     "inputsInline": true,
    //     "output": "Nat",
    // },
    {
        "type": "nat",
        "message0": "%1",
        "args0": [
            {
                "type": "field_number",
                "name": "NUM",
                "min": 0,
                "precision": 1
            },
        ],
        "colour": COLOUR_EXPRESSIONS,
        "output": ["Nat", "Expression"],
    },
    {
        "type": "successor",
        "message0": "S %1",
        "args0": [
            {
                "type": "input_value",
                "name": "NUM",
                "check": "Nat",
            },
        ],
        "colour": COLOUR_EXPRESSIONS,
        "output": ["Nat", "Expression"],
    },
    {
        "type": "underscore",
        "message0": "_",
        "colour": COLOUR_TACTICS,
        "output": ["IntroPatternIdentifier", "Underscore"],
    },
]);

Blockly.Blocks['underscore'].getCaseConstrBlocks = function() {
    return [];
}

// Bernard: This is an example of a dropdown changing the shape of the block.
// See https://developers.google.com/blockly/guides/create-custom-blocks/fields/built-in-fields/dropdown#creating_a_dropdown_validator

Blockly.Blocks['destruct_variants'] = {
    init: function () {
        const options = [
            ['has neither', 'NEITHER'],
            ['has statement', 'STATEMENT'],
            ['has value', 'VALUE'],
        ];

        this.setColour(COLOUR_TACTICS);
        this.setNextStatement("Tactic");
        this.setPreviousStatement("Tactic");
        this.appendDummyInput()
            .appendField("destruct")
            .appendField(new Blockly.FieldVariable("item"))
            .appendField(new Blockly.FieldDropdown(options, this.validate), 'MODE');
    },
    validate: function (newValue) {
        this.getSourceBlock().updateConnections(newValue);
        return newValue;
    },
    updateConnections: function (newValue) {
        this.removeInput('STATEMENT', /* no error */ true);
        this.removeInput('VALUE', /* no error */ true);
        if (newValue === 'STATEMENT') {
            this.appendStatementInput('STATEMENT');
        } else if (newValue === 'VALUE') {
            this.appendValueInput('VALUE');
        }
    }
};

// Blockly.Blocks['destruct_conjunction'] = {
//     init: function () {
//         this.appendDummyInput()
//             .appendField("destruct")
//             .appendField(new Blockly.FieldDropdown([["[Select variable]", "[Select variable]"]]), "HYPOTHESIS")
//             .appendField("as [");
//         this.appendValueInput("LEFT")
//             .setCheck("IntroPattern");
//         this.appendValueInput("RIGHT")
//             .setCheck("IntroPattern");
//         this.appendDummyInput()
//             .appendField("]");
//         this.setColour(COLOUR_TACTICS);
//         this.setNextStatement("Tactic");
//         this.setPreviousStatement("Tactic");
//         this.setInputsInline(true);
//     },
//     mutationToDom: hypothesisDropdownMutationToDom,
//     domToMutation: hypothesisDropdownDomToMutation,
//     getIdentifiers: function () {
//         const leftBlock = this.getInputTargetBlock("LEFT");
//         const leftIdentifiers = leftBlock ? leftBlock.getIdentifiers() : [];
//         const rightBlock = this.getInputTargetBlock("RIGHT");
//         const rightIdentifiers = rightBlock ? rightBlock.getIdentifiers() : [];
//         return [...leftIdentifiers, ...rightIdentifiers];
//     },
// };


// Blockly.Blocks['exact'].mutationToDom = hypothesisDropdownMutationToDom;
// Blockly.Blocks['exact'].domToMutation = hypothesisDropdownDomToMutation;

/**
 * Saves the options of the dropdown to XML.
 * @returns {Element}
 */
function varDropdownMutationToDom() {
    const container = Blockly.utils.xml.createElement('mutation');
    const options = this.getField("VAR").getOptions(false);
    container.setAttribute('options', JSON.stringify(options));
    return container;
}

/**
 * Restores the options for the dropdown from XML.
 */
function varDropdownDomToMutation(xmlElement) {
    const options = xmlElement.getAttribute('options');
    const parsedOptions = JSON.parse(options);
    if (parsedOptions) {
        this.getField("VAR").menuGenerator_ = parsedOptions;
    }
}

/**
 * Saves the options of the dropdown to XML.
 * @returns {Element}
 */
function typeDropdownMutationToDom() {
    const container = Blockly.utils.xml.createElement('mutation');
    const options = this.getField("TYPE0").getOptions(false);
    container.setAttribute('options', JSON.stringify(options));
    return container;
}

/**
 * Restores the options for the dropdown from XML.
 */
function typeDropdownDomToMutation(xmlElement) {
    const options = xmlElement.getAttribute('options');
    const parsedOptions = JSON.parse(options);
    if (parsedOptions) {
        for (let i = 0; i < this.typeCount_; i++) {
            this.getField("TYPE" + i).menuGenerator_ = parsedOptions;
        }
    }
}

Blockly.Blocks['variable_dropdown'].mutationToDom = varDropdownMutationToDom;
Blockly.Blocks['variable_dropdown'].domToMutation = varDropdownDomToMutation;
Blockly.Blocks['variable_dropdown'].getVarFields = function () {
    return [this.getField("VAR")];
}

Blockly.Blocks['conjunctive_pattern'].getNumBranches = function () {
    let sum = 0;
    let multiplication = 1;

    const left = this.getInputTargetBlock("LEFT");
    const right = this.getInputTargetBlock("RIGHT");

    if (left && left.getNumBranches) {
        const leftBranches = left.getNumBranches();
        sum += leftBranches;
        if (leftBranches !== 0) {
            multiplication *= leftBranches;
        }
    }
    if (right && right.getNumBranches) {
        const rightBranches = right.getNumBranches();
        sum += rightBranches;
        if (rightBranches !== 0) {
            multiplication *= rightBranches;
        }
    }
    if (sum === 0) {
        return 0;
    } else {
        return multiplication;
    }
}

Blockly.Blocks['disjunctive_pattern'].getNumBranches = function () {
    let count = 0;
    const left = this.getInputTargetBlock("LEFT");
    const right = this.getInputTargetBlock("RIGHT");
    if (left && left.getNumBranches && left.getNumBranches() > 0) {
        count += left.getNumBranches();
    } else {
        count++;
    }
    if (right && right.getNumBranches && right.getNumBranches() > 0) {
        count += right.getNumBranches();
    } else {
        count++;
    }
    return count;
}



// LEFT * RIGHT (multiply)
Blockly.Blocks['conjunctive_pattern'].getIdentifiersFromIntroPattern = function () {
    // CARTESIAN PRODUCT
    // [[A]] [[B]] --> [[A, B]]
    // [[A] [B]] [[C] [D]] --> [[A C] [A D] [B C] [B D]]
    // [[A] [B] [C]]  [[D] [E] [F]]  -->  [[A D] [A E] [A F] [B D] [B E] [B F] [C D] [C E] [C F]]
    // [[A] [B]] [[]] --> [[A] [B]]
    // TODO: (A /\ (B \/ C)) \/ (D /\ E)
    const leftBlock = this.getInputTargetBlock("LEFT");
    const leftIdentifiers = leftBlock ? leftBlock.getIdentifiersFromIntroPattern() : [[]];
    const rightBlock = this.getInputTargetBlock("RIGHT");
    const rightIdentifiers = rightBlock ? rightBlock.getIdentifiersFromIntroPattern() : [[]];
    // const identifiers = [];
    // for (let leftBranchIdentifiers of leftIdentifiers) {
    //     for (let rightBranchIdentifiers of rightIdentifiers) {
    //         identifiers.push([...leftBranchIdentifiers, ...rightBranchIdentifiers]);
    //     }
    // }
    return cartesianProduct(leftIdentifiers, rightIdentifiers);
}

Blockly.Blocks['disjunctive_pattern'].getIdentifiersFromIntroPattern = function () {
    const leftBlock = this.getInputTargetBlock("LEFT");
    const leftIdentifiers = leftBlock ? leftBlock.getIdentifiersFromIntroPattern() : [[]];  // [["A", "B"], ["C", "D"]]
    const rightBlock = this.getInputTargetBlock("RIGHT");
    const rightIdentifiers = rightBlock ? rightBlock.getIdentifiersFromIntroPattern() : [[]];
    return [...leftIdentifiers, ...rightIdentifiers];
}

Blockly.Blocks['intro_pattern_identifier'] = {
    init: function () {
        const prefix = "H";
        let index = 0;

        // Name variables incrementally each time they are added to the workspace (H_0, H_1, H_2, ...)
        // TODO: Make this happen for duplicating blocks also
        const names = [];
        const blocks = Blockly.getMainWorkspace().getAllBlocks(false);
        for (block of blocks) {
            if (block === this) {
                continue;
            }
            if (block.type === "intro" || block.type === "intro_pattern_identifier") {
                const name = block.getFieldValue("VAR");
                names.push(name);
            }
        }

        while (names.includes(prefix + index)) {
            index++;
        }

        const nameField = new Blockly.FieldTextInput(prefix + index, variableValidator);
        nameField.setSpellcheck(false);
        // HACK to make sure that traversal is done only after text field has been edited completely.
        // Don't traverse during intermediate states.
        // See https://github.com/google/blockly/issues/4350
        nameField.onFinishEditing_ = completeVariableRenaming;

        this.setColour(COLOUR_TACTICS);
        this.setOutput(true, "IntroPatternIdentifier");

        this.appendDummyInput()
            .appendField(nameField, 'VAR');
    },
    getIdentifiersFromIntroPattern: function () {
        return [[this.getFieldValue("VAR")]];
    },
};


Blockly.Blocks['intro'] = {
    init: function () {
        const prefix = "H";
        let index = 0;

        // Name variables incrementally each time they are added to the workspace (H_0, H_1, H_2, ...)
        const names = [];
        const blocks = Blockly.getMainWorkspace().getAllBlocks(false);
        for (block of blocks) {
            if (block === this) {
                continue;
            }
            if (block.type === "intro" || block.type === "intro_pattern_identifier") {
                const name = block.getFieldValue("VAR");
                names.push(name);
            }
        }

        while (names.includes(prefix + index)) {
            index++;
        }

        const nameField = new Blockly.FieldTextInput(prefix + index, variableValidator);
        nameField.setSpellcheck(false);
        // HACK to make sure that traversal is done only after text field has been edited completely.
        // Don't traverse during intermediate states.
        // See https://github.com/google/blockly/issues/4350
        nameField.onFinishEditing_ = completeVariableRenaming;

        this.setColour(COLOUR_TACTICS);
        this.setNextStatement("Tactic");
        this.setPreviousStatement("Tactic");

        this.appendDummyInput()
            .appendField("intro")
            .appendField(nameField, 'VAR');
    },
};
