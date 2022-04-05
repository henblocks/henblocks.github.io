// Referenced from https://blocklycodelabs.dev/codelabs/custom-generator/index.html

function indent(text) {
    return "  " + text.replace(/\n/g, "\n  ");
}

function sanitize(variable) {
    switch (variable) {
        case "[Select variable]":
            return "???";
        case "[Select constructor]":
            return "???";
        default:
            return variable;
    }
}

const coqGenerator = new Blockly.Generator('Coq');

coqGenerator.PRECEDENCE = 0;

coqGenerator["theorem"] = function (block) {
    const theoremName = block.getFieldValue("VAR");
    // const statements = codelabGenerator.statementToCode(block, 'STATEMENTS');
    const proposition = coqGenerator.valueToCode(block, "PROPOSITION", coqGenerator.PRECEDENCE);
    const nextBlock = coqGenerator.blockToCode(block.getNextBlock());
    return `Theorem ${theoremName} :\n${indent(proposition)}.\n${nextBlock}`;
}

coqGenerator["proof"] = function (block) {
    const statements = coqGenerator.statementToCode(block, 'STATEMENTS');
    return `Proof.\n${statements}Qed.\n`;
}

coqGenerator["intro"] = function (block) {
    // const varName = Blockly.Coq.nameDB_.getName(block.getFieldValue('VAR'), Blockly.VARIABLE_CATEGORY_NAME);
    const varName = block.getFieldValue('VAR');
    const nextBlock = coqGenerator.blockToCode(block.getNextBlock());
    return `intro ${varName}.\n${nextBlock}`;
}

coqGenerator["exact"] = function (block) {
    // const varName = Blockly.Coq.nameDB_.getName(block.getFieldValue('VAR'), Blockly.VARIABLE_CATEGORY_NAME);
    const varExpression = coqGenerator.valueToCode(block, "VAR", coqGenerator.PRECEDENCE);
    const nextBlock = coqGenerator.blockToCode(block.getNextBlock());
    return `exact ${varExpression}.\n${nextBlock}`;
}

coqGenerator["revert"] = function (block) {
    const varName = Blockly.Coq.nameDB_.getName(block.getFieldValue('VAR'), Blockly.VARIABLE_CATEGORY_NAME);
    const nextBlock = coqGenerator.blockToCode(block.getNextBlock());
    return `revert ${varName}.\n${nextBlock}`;
}

coqGenerator["rewrite"] = function (block) {
    const arrow = (block.getFieldValue("ARROW") === "LTR") ? "->" : "<-";
    const varExpression = coqGenerator.valueToCode(block, "VAR", coqGenerator.PRECEDENCE);
    const nextBlock = coqGenerator.blockToCode(block.getNextBlock());
    return `rewrite ${arrow} ${varExpression}.\n${nextBlock}`;
}

coqGenerator["unfold"] = function (block) {
    const varName = Blockly.Coq.nameDB_.getName(block.getFieldValue('VAR'), Blockly.VARIABLE_CATEGORY_NAME);
    const nextBlock = coqGenerator.blockToCode(block.getNextBlock());
    return `unfold ${varName}.\n${nextBlock}`;
}

coqGenerator["destruct_conjunction"] = function (block) {
    const hypothesis = Blockly.Coq.nameDB_.getName(block.getFieldValue('HYPOTHESIS'), Blockly.VARIABLE_CATEGORY_NAME);
    const left = coqGenerator.valueToCode(block, "LEFT", coqGenerator.PRECEDENCE);
    const right = coqGenerator.valueToCode(block, "RIGHT", coqGenerator.PRECEDENCE);
    const nextBlock = coqGenerator.blockToCode(block.getNextBlock());
    return `destruct ${hypothesis} as [${left} ${right}].\n${nextBlock}`;
}

// coqGenerator["induction"] = function (block) {
//     const var1 = Blockly.Coq.nameDB_.getName(block.getFieldValue('VAR1'), Blockly.VARIABLE_CATEGORY_NAME);
//     const var2 = Blockly.Coq.nameDB_.getName(block.getFieldValue('VAR2'), Blockly.VARIABLE_CATEGORY_NAME);
//     const var3 = Blockly.Coq.nameDB_.getName(block.getFieldValue('VAR3'), Blockly.VARIABLE_CATEGORY_NAME);
//
//     const nextBlock = coqGenerator.blockToCode(block.getNextBlock());
//     const statements_base = coqGenerator.statementToCode(block, 'STATEMENTS_BASE');
//     const code_base = !statements_base ? "-\n" : "-" + statements_base.slice(1);
//     const statements_ih = coqGenerator.statementToCode(block, 'STATEMENTS_IH');
//     const code_ih = !statements_ih ? "-\n" : "-" + statements_ih.slice(1);
//     return `induction ${var1} as [|${var2} ${var3}].\n${code_base}${code_ih}${nextBlock}`;
// }

coqGenerator["reflexivity"] = function (block) {
    const nextBlock = coqGenerator.blockToCode(block.getNextBlock());
    return `reflexivity.\n${nextBlock}`;
}

coqGenerator["simpl"] = function (block) {
    const nextBlock = coqGenerator.blockToCode(block.getNextBlock());
    return `simpl.\n${nextBlock}`;
}

coqGenerator["left_right"] = function (block) {
    const command = block.getFieldValue("COMMAND");
    const nextBlock = coqGenerator.blockToCode(block.getNextBlock());
    return `${command}.\n${nextBlock}`;
}

// coqGenerator["right"] = function (block) {
//     const nextBlock = coqGenerator.blockToCode(block.getNextBlock());
//     return `right.\n${nextBlock}`;
// }

coqGenerator["symmetry"] = function (block) {
    const nextBlock = coqGenerator.blockToCode(block.getNextBlock());
    return `symmetry.\n${nextBlock}`;
}

coqGenerator["f_equal"] = function (block) {
    const nextBlock = coqGenerator.blockToCode(block.getNextBlock());
    return `f_equal.\n${nextBlock}`;
}

coqGenerator["split"] = function (block) {
    const nextBlock = coqGenerator.blockToCode(block.getNextBlock());
    const statements_left = coqGenerator.statementToCode(block, 'STATEMENTS_LEFT');
    const code_left = !statements_left ? "-\n" : "-" + statements_left.slice(1);
    const statements_right = coqGenerator.statementToCode(block, 'STATEMENTS_RIGHT');
    const code_right = !statements_right ? "-\n" : "-" + statements_right.slice(1);
    return `split.\n${code_left}${code_right}${nextBlock}`;
}

coqGenerator["variable"] = function (block) {
    const varName = Blockly.Coq.nameDB_.getName(block.getFieldValue('VAR'), Blockly.VARIABLE_CATEGORY_NAME);
    return [varName, coqGenerator.PRECEDENCE];
}

// codelabGenerator["function_application"] = function (block) {
//     const fun = block.getFieldValue("FUN");
//     const arg = block.getFieldValue("ARG");
//     return [`${fun} ${arg}`, codelabGenerator.PRECEDENCE];
// }

// codelabGenerator["refine"] = function (block) {
//     const nextBlock = codelabGenerator.blockToCode(block.getNextBlock());
//     const value = codelabGenerator.valueToCode(block, "VALUE", codelabGenerator.PRECEDENCE);
//     return `refine (${value}).\n${nextBlock}`;
// }

// codelabGenerator["match"] = function (block) {
//     const var1 = Blockly.Coq.nameDB_.getName(block.getFieldValue('VAR1'), Blockly.VARIABLE_CATEGORY_NAME);
//     const case1 = block.getFieldValue("CASE1");
//     const result1 = block.getFieldValue("RESULT1");
//     return [`match ${var1} with\n        | ${case1} => ${result1}\n        end`, codelabGenerator.PRECEDENCE];
// }
// TODO: Make whitespace variable

coqGenerator["conjunction_disjunction"] = function (block) {
    const left = coqGenerator.valueToCode(block, "LEFT", coqGenerator.PRECEDENCE);
    const right = coqGenerator.valueToCode(block, "RIGHT", coqGenerator.PRECEDENCE);
    const operator = block.getFieldValue("OPERATOR");
    return [`${left} ${operator} ${right}`, coqGenerator.PRECEDENCE];
}

// coqGenerator["conjunction"] = function (block) {
//     const left = coqGenerator.valueToCode(block, "LEFT", coqGenerator.PRECEDENCE);
//     const right = coqGenerator.valueToCode(block, "RIGHT", coqGenerator.PRECEDENCE);
//     return [`${left} /\\ ${right}`, coqGenerator.PRECEDENCE];
// }
//
// coqGenerator["disjunction"] = function (block) {
//     const left = coqGenerator.valueToCode(block, "LEFT", coqGenerator.PRECEDENCE);
//     const right = coqGenerator.valueToCode(block, "RIGHT", coqGenerator.PRECEDENCE);
//     return [`${left} \\/ ${right}`, coqGenerator.PRECEDENCE];
// }

coqGenerator["equality"] = function (block) {
    const left = coqGenerator.valueToCode(block, "LEFT", coqGenerator.PRECEDENCE);
    const right = coqGenerator.valueToCode(block, "RIGHT", coqGenerator.PRECEDENCE);
    return [`${left} = ${right}`, coqGenerator.PRECEDENCE];
}

coqGenerator["implies"] = function (block) {
    const left = coqGenerator.valueToCode(block, "LEFT", coqGenerator.PRECEDENCE);
    const right = coqGenerator.valueToCode(block, "RIGHT", coqGenerator.PRECEDENCE);
    return [`${left} -> ${right}`, coqGenerator.PRECEDENCE];
}

coqGenerator["forall"] = function (block) {
    let index = 0;
    const binders = []
    let binder = coqGenerator.valueToCode(block, "BINDER" + index, coqGenerator.PRECEDENCE);
    while (binder) {
        binders.push(binder);
        index++;
        binder = coqGenerator.valueToCode(block, "BINDER" + index, coqGenerator.PRECEDENCE);
    }
    const proposition = coqGenerator.valueToCode(block, "PROPOSITION", coqGenerator.PRECEDENCE);
    const binderCode = binders.map(binder => `(${binder})`).join(" ");

    const command = block.getFieldValue("COMMAND");
    return [`${command} ${binderCode},\n${indent(proposition)}`, coqGenerator.PRECEDENCE];
}

coqGenerator["binder"] = function (block) {
    let index = 0;
    const variables = [];
    let variable = block.getFieldValue("VAR" + index);
    while (variable) {
        variables.push(variable);
        index++;
        variable = block.getFieldValue("VAR" + index);
    }
    const varCode = variables.join(" ");

    index = 0;
    const types = [];
    let type = block.getFieldValue("TYPE" + index);
    while (type) {
        types.push(type);
        index++;
        type = block.getFieldValue("TYPE" + index);
    }
    const typeCode = types.join(" -> ");
    return [`${varCode}: ${typeCode}`, coqGenerator.PRECEDENCE];
}


coqGenerator["variable_dropdown"] = function (block) {
    const name = block.getFieldValue("VAR");
    return [`${name}`, coqGenerator.PRECEDENCE];
}

coqGenerator["variable_dropdown_multiple"] = function (block) {
    const vars = [];
    for (let i = 0; i < block.varCount_; i++) {
        const variable = block.getFieldValue("VAR" + i);
        vars.push(sanitize(variable));
    }
    return [`(${vars.join(" ")})`, coqGenerator.PRECEDENCE];
}

coqGenerator["not"] = function (block) {
    const proposition = coqGenerator.valueToCode(block, "PROPOSITION", coqGenerator.PRECEDENCE);
    return [`~ ${proposition}`, coqGenerator.PRECEDENCE];
}

coqGenerator["math_operation"] = function (block) {
    const left = coqGenerator.valueToCode(block, "LEFT", coqGenerator.PRECEDENCE);
    const right = coqGenerator.valueToCode(block, "RIGHT", coqGenerator.PRECEDENCE);
    const operator = block.getFieldValue("OPERATOR");
    return [`${left} ${operator} ${right}`, coqGenerator.PRECEDENCE];
}

// coqGenerator["addition"] = function (block) {
//     const left = coqGenerator.valueToCode(block, "LEFT", coqGenerator.PRECEDENCE);
//     const right = coqGenerator.valueToCode(block, "RIGHT", coqGenerator.PRECEDENCE);
//     return [`${left} + ${right}`, coqGenerator.PRECEDENCE];
// }
//
// coqGenerator["multiplication"] = function (block) {
//     const left = coqGenerator.valueToCode(block, "LEFT", coqGenerator.PRECEDENCE);
//     const right = coqGenerator.valueToCode(block, "RIGHT", coqGenerator.PRECEDENCE);
//     return [`${left} x ${right}`, coqGenerator.PRECEDENCE];
// }

coqGenerator["successor"] = function (block) {
    const num = coqGenerator.valueToCode(block, "NUM", coqGenerator.PRECEDENCE);
    return [`S ${num}`, coqGenerator.PRECEDENCE];
}

coqGenerator["nat"] = function (block) {
    const num = block.getFieldValue("NUM");
    return [`${num}`, coqGenerator.PRECEDENCE];
}

coqGenerator["intro_pattern_identifier"] = function (block) {
    const name = block.getFieldValue("VAR");
    return [`${name}`, coqGenerator.PRECEDENCE];
}

coqGenerator["conjunctive_pattern"] = function (block) {
    const left = coqGenerator.valueToCode(block, "LEFT", coqGenerator.PRECEDENCE);
    const right = coqGenerator.valueToCode(block, "RIGHT", coqGenerator.PRECEDENCE);
    return [`[${left} ${right}]`, coqGenerator.PRECEDENCE];
}

coqGenerator["disjunctive_pattern"] = function (block) {
    const left = coqGenerator.valueToCode(block, "LEFT", coqGenerator.PRECEDENCE);
    const right = coqGenerator.valueToCode(block, "RIGHT", coqGenerator.PRECEDENCE);
    return [`[${left} | ${right}]`, coqGenerator.PRECEDENCE];
}

coqGenerator["multiple_identifier"] = function (block) {
    let index = 0;
    const variables = []
    let variable = coqGenerator.valueToCode(block, "VAR" + index, coqGenerator.PRECEDENCE);
    while (variable) {
        variables.push(variable);
        index++;
        variable = coqGenerator.valueToCode(block, "VAR" + index, coqGenerator.PRECEDENCE);
    }
    const varCode = variables.join(" ");
    return [`${varCode}`, coqGenerator.PRECEDENCE];
}

// coqGenerator["destruct_disjunction"] = function (block) {
//     return "";
// }

coqGenerator["conjunctive_pattern_multiple"] = function (block) {
    let index = 0;
    const patterns = []
    let pattern = coqGenerator.valueToCode(block, "PATTERN" + index, coqGenerator.PRECEDENCE);
    while (pattern) {
        patterns.push(pattern);
        index++;
        pattern = coqGenerator.valueToCode(block, "PATTERN" + index, coqGenerator.PRECEDENCE);
    }
    const code = patterns.join(" ");
    return [`[${code}]`, coqGenerator.PRECEDENCE];
}


coqGenerator["disjunctive_pattern_multiple"] = function (block) {
    let index = 0;
    const patterns = []
    let pattern = coqGenerator.valueToCode(block, "PATTERN" + index, coqGenerator.PRECEDENCE);
    while (pattern) {
        patterns.push(pattern);
        index++;
        pattern = coqGenerator.valueToCode(block, "PATTERN" + index, coqGenerator.PRECEDENCE);
    }
    const code = patterns.join(" | ");
    return [`[${code}]`, coqGenerator.PRECEDENCE];
}

coqGenerator["destruct"] = function (block) {
    const varName = block.getFieldValue('VAR');
    const pattern = coqGenerator.valueToCode(block, "PATTERN", coqGenerator.PRECEDENCE);
    const nextBlock = coqGenerator.blockToCode(block.getNextBlock());
    const branches = [];

    for (let i = 0; i < block.branchCount_; i++) {
        const branch = coqGenerator.statementToCode(block, 'STATEMENTS' + i);
        const code = !branch ? "-\n" : "-" + branch.slice(1);
        branches.push(code);
    }
    const branchesCode = branches.join("");
    return `destruct ${sanitize(varName)} as ${pattern}.\n${branchesCode}${nextBlock}`;
}

coqGenerator["induction"] = function (block) {
    const varName = block.getFieldValue('VAR');
    const pattern = coqGenerator.valueToCode(block, "PATTERN", coqGenerator.PRECEDENCE);
    const nextBlock = coqGenerator.blockToCode(block.getNextBlock());
    const branches = [];

    for (let i = 0; i < block.branchCount_; i++) {
        const branch = coqGenerator.statementToCode(block, 'STATEMENTS' + i);
        const code = !branch ? "-\n" : "-" + branch.slice(1);
        branches.push(code);
    }
    const branchesCode = branches.join("");
    return `induction ${sanitize(varName)} as ${pattern}.\n${branchesCode}${nextBlock}`;
}

coqGenerator["inductive"] = function (block) {
    const inductiveName = block.getFieldValue("VAR");
    const constructors = [];
    for (let i = 0; i < block.branchCount_; i++) {
        const branch = coqGenerator.valueToCode(block, 'BRANCH' + i, coqGenerator.PRECEDENCE);
        constructors.push(branch);
    }
    const constructorCode = constructors.join("\n");
    return `Inductive ${inductiveName} :=\n${constructorCode}.\n`;
}

coqGenerator["constructor_definition"] = function (block) {
    const name = block.getFieldValue("VAR");
    const binders = []

    for (let i = 0; i < block.binderCount_; i++) {
        const binder = coqGenerator.valueToCode(block, 'BINDER' + i, coqGenerator.PRECEDENCE);
        binders.push(binder);
    }

    let binderCode = binders.map(binder => `(${binder})`).join(" ");
    if (binderCode !== "") {
        binderCode = " " + binderCode;
    }
    return [`| ${name}${binderCode}`, coqGenerator.PRECEDENCE];
}

coqGenerator["definition_or_fixpoint"] = function (block) {
    const command = block.getFieldValue("COMMAND");
    const name = block.getFieldValue("VAR");
    const binders = []

    for (let i = 0; i < block.binderCount_; i++) {
        const binder = coqGenerator.valueToCode(block, 'BINDER' + i, coqGenerator.PRECEDENCE);
        binders.push(binder);
    }

    let binderCode = binders.map(binder => `(${binder})`).join(" ");
    if (binderCode !== "") {
        binderCode = " " + binderCode;
    }
    const typeCode = block.getFieldValue("TYPE");

    const expression = coqGenerator.valueToCode(block, "EXPRESSION", coqGenerator.PRECEDENCE);
    return `${command} ${name}${binderCode} : ${typeCode} :=\n${indent(expression)}.\n`;
}

coqGenerator["match"] = function (block) {
    const variable = block.getFieldValue("VAR");
    const branches = [];
    for (let i = 0; i < block.branchCount_; i++) {
        branches.push("\n| ");
        const caseCode = coqGenerator.valueToCode(block, "CASE" + i, coqGenerator.PRECEDENCE);
        branches.push(caseCode);
        branches.push(" => ");
        const result = coqGenerator.valueToCode(block, "RESULT" + i, coqGenerator.PRECEDENCE);
        branches.push(result);
    }
    const branchCode = branches.join("");
    return [`match ${sanitize(variable)} with${branchCode}\nend`, coqGenerator.PRECEDENCE];
}

coqGenerator["case_constructor"] = function (block) {
    const variable = block.getFieldValue("VAR");
    const children = [];
    for (let i = 0; i < block.argCount_; i++) {
        const childCode = coqGenerator.valueToCode(block, "ARG" + i, coqGenerator.PRECEDENCE);
        children.push(childCode);
    }
    const code = (children.length === 0 ? "" : " ") + children.join(" ");
    return [`${sanitize(variable)}${code}`, coqGenerator.PRECEDENCE];
}

coqGenerator["case_identifier"] = function (block) {
    const variable = block.getFieldValue("VAR");
    return [`${variable}`, coqGenerator.PRECEDENCE];
}

coqGenerator["true_or_false_proposition"] = function (block) {
    return [block.getFieldValue('BOOL'), coqGenerator.PRECEDENCE];
}

coqGenerator["true_or_false_expression"] = function (block) {
    return [block.getFieldValue('BOOL'), coqGenerator.PRECEDENCE];
}
