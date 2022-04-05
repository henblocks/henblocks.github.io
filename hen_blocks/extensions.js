// TODO: Unify this with traverseTactics()
// Amendment: Not possible to unify with traverseTactics()
// function calculateHypothesesIdentifiers(targetBlock) {
//     const options = [];
//     const removed = [];
//     if (targetBlock) {
//         let block = targetBlock.getPreviousBlock();
//         while (block && block.type !== "proof") {
//             if (block.type === "intro") {
//                 const selectedOption = block.getFieldValue("VAR");
//                 options.push(selectedOption);
//             } else if (block.type === "destruct_conjunction") {
//                 const selectedOption = block.getFieldValue("HYPOTHESIS");
//                 removed.push(selectedOption);
//
//                 const destructIdentifiers = getIdentifiersFromDestructConjunction(block);
//                 destructIdentifiers.reverse().forEach(identifier => options.push(identifier));
//             }
//             block = block.getPreviousBlock();
//         }
//     }
//     const filteredOptions = options.filter(option => !removed.includes(option));
//     return filteredOptions.reverse();
// }

// function getIdentifiersFromDestructConjunction(block) {
//     if (block.type === "intro_pattern_identifier") {
//         return [block.getFieldValue("VAR")];
//     }
//     const left = block.getInputTargetBlock("LEFT");
//     const leftIdentifiers = getIdentifiersFromDestructConjunction(left);
//     const right = block.getInputTargetBlock("RIGHT");
//     const rightIdentifiers = getIdentifiersFromDestructConjunction(right);
//     return [...leftIdentifiers, ...rightIdentifiers];
// }

// function calculateForallExistsIdentifiers(targetBlock) {
//     const identifiers = [];
//     if (targetBlock) {
//         let block = targetBlock.getSurroundParent();
//         while (block && block.type !== "theorem") {
//             if (block.type === "forall" || block.type === "exists") {
//                 identifiers.push(block.getIdentifiers());
//             }
//             block = block.getSurroundParent();
//         }
//     }
//     return identifiers.reverse().flatten();
// }


// See Dynamic Dropdowns:
// https://developers.google.com/blockly/guides/create-custom-blocks/fields/built-in-fields/dropdown#dynamic_dropdowns
// Blockly.Extensions.register('hypotheses_extension', function () {
//     this.getInput('INPUT')
//         .appendField(getHypothesesDropdown(), 'HYPOTHESIS');
// });
//
// function getHypothesesDropdown() {
//     return new Blockly.FieldDropdown(
//         function () {
//             const block = this.getSourceBlock();
//             const options = calculateHypothesesIdentifiers(block).map(value => [value, value]);
//             if (options.length === 0) {
//                 return [["[Select variable]", "[Select variable]"]];
//             }
//             return options;
//         }
//     )
// }


// No longer needed because done in traverseTactics()
// Blockly.Extensions.register('hypotheses_on_change', function () {
//     this.setOnChange(function (changeEvent) {
//         const selectedOption = this.inputList[0].fieldRow[1].selectedOption_[0];
//         if (selectedOption === "[Select variable]") {
//             this.setWarningText("Please select a variable");
//         } else {
//             const options = calculateHypothesesIdentifiers(this);
//             if (options.some(optionPair => optionPair[0] === selectedOption)) {
//                 this.setWarningText(null);
//             } else {
//                 this.setWarningText("Please ensure the selected variable has been defined");
//             }
//         }
//     });
// });

// Blockly.Extensions.register('variable_extension', function () {
//     this.getInput('INPUT')
//         .appendField(new Blockly.FieldDropdown(function () {
//             const block = this.getSourceBlock();
//             const options = calculateForallExistsIdentifiers(block).map(value => [value, value]);
//             if (options.length === 0) {
//                 return [["[Select variable]", "[Select variable]"]];
//             }
//             return options;
//         }), 'VAR');
// });

// Blockly.Extensions.register('variable_on_change', function () {
//     this.setOnChange(function (changeEvent) {
//         const selectedOption = this.getFieldValue("VAR");
//         if (selectedOption === "[Select variable]") {
//             this.setWarningText("Please select a variable");
//         } else {
//             const options = calculateForallExistsIdentifiers(this);
//             if (options.includes(selectedOption)) {
//                 this.setWarningText(null);
//             } else {
//                 this.setWarningText("Please ensure the selected variable has been defined");
//             }
//         }
//     });
// });
