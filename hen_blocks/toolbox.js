// Red: 0
//     Orange: 30
// Yellow: 60
// Green: 110
//     Teal: 170
// Blue: 220
// Indigo: 260
//     Violet: 300

const COLOUR_COMMANDS = 220;
const COLOUR_EXPRESSIONS = 30;
const COLOUR_PROPOSITIONS = 0;
const COLOUR_TACTICS = 110;
const COLOUR_VAR = 260;

const coqToolbox = `
<xml id="toolbox" style="display: none">
    <category name="Commands" colour="${COLOUR_COMMANDS}">
        <block type="definition_or_fixpoint">
            <value name="BINDER0">
                <block type="binder" />
            </value>
        </block>
        <block type="inductive">
            <value name="BRANCH0">
                <block type="constructor_definition">
                    <field name="VAR">constructor_name0</field>
                </block>
            </value>
            <value name="BRANCH1">
                <block type="constructor_definition">
                    <field name="VAR">constructor_name1</field>
                </block>
            </value>
        </block>
        <!-- <block type="constructor_definition"/> -->
        <block type="theorem"/>
        <block type="proof"/>
    </category>
    <category name="Expressions" colour="${COLOUR_EXPRESSIONS}">
        <label text="Pattern Matching"></label>
        <block type="match">
            <value name="CASE0">
                <block type="case_constructor" />
                <shadow type="case_constructor" />
            </value>
            <value name="CASE1">
                <block type="case_constructor" />
                <shadow type="case_constructor" />
            </value>
        </block>
        <block type="case_constructor"/>
        <block type="case_identifier"/>
        <sep gap="50"></sep>
        <label text="Other Expressions"></label>
        <block type="nat"/>
        <block type="successor"/>
        <block type="math_operation">
            <field name="OPERATOR">+</field>
        </block>
        <!-- <block type="math_operation"> -->
        <!--     <field name="OPERATOR">*</field> -->
        <!-- </block> -->
        <block type="true_or_false_expression"/>
        <block type="variable_dropdown"/>
        <block type="variable_dropdown_multiple"/>
    </category>
    <category name="Propositions" colour="${COLOUR_PROPOSITIONS}">
        <block type="forall">
            <value name="BINDER0">
                <block type="binder">
                </block>
                <shadow type="binder">
                </shadow>
            </value>
        </block>
        <!-- <block type="binder"/> -->
        <block type="implies"/>
        <block type="conjunction_disjunction">
            <field name="OPERATOR">/\\</field>
        </block>
        <!-- <block type="conjunction_disjunction"> -->
        <!--     <field name="OPERATOR">\\/</field> -->
        <!-- </block> -->
        <block type="equality"/>
        <block type="true_or_false_proposition"/>
        <block type="not"/>
        <!-- <block type="binder_dialog"/> -->
        <block type="variable_dropdown"/>
        <block type="variable_dropdown_multiple"/>
    </category>
    <category name="Tactics" colour="${COLOUR_TACTICS}">
        <block type="variable_dropdown"/>
        <block type="variable_dropdown_multiple"/>
        <label text="Managing Context"></label>
        <block type="intro"/>
        <block type="revert"/>
        
        <label text="Solving Goals"></label>
        <block type="reflexivity"/>
        <block type="exact">
            <value name="VAR">
                <block type="variable_dropdown" />
                <shadow type="variable_dropdown" />
            </value>
        </block>
        
        <label text="Transforming Goals/Hypotheses"></label>
        
        <block type="rewrite">
            <value name="VAR">
                <block type="variable_dropdown_multiple" />
                <shadow type="variable_dropdown_multiple" />
            </value>
        </block>
        <block type="unfold"/>
        <block type="symmetry"/>
        <block type="simpl"/>
        <block type="f_equal"/>
        
        <label text="Transforming con/disjunctions in Goals"></label>
        <block type="left_right"/>
        <block type="split"/>
        
        <label text="Transforming con/disjunctions in Hypotheses"></label>
        <block type="destruct">
            <value name="PATTERN">
                <block type="conjunctive_pattern">
                    <value name="LEFT">
                        <block type="intro_pattern_identifier">
                            <field name="VAR">H_left</field>
                        </block>
                    </value>
                    <value name="RIGHT">
                        <block type="intro_pattern_identifier">
                            <field name="VAR">H_right</field>
                        </block>
                    </value>
                </block>
            </value>
        </block>
        <block type="destruct">
            <value name="PATTERN">
                <block type="disjunctive_pattern">
                    <value name="LEFT">
                        <block type="intro_pattern_identifier">
                            <field name="VAR">H_left</field>
                        </block>
                    </value>
                    <value name="RIGHT">
                        <block type="intro_pattern_identifier">
                            <field name="VAR">H_right</field>
                        </block>
                    </value>
                </block>
            </value>
        </block>
        <sep gap="90"></sep>
        <block type="induction"/>
        <label text="Intro Patterns"></label>
        <block type="intro_pattern_identifier"/>
        <block type="conjunctive_pattern"/>
        <block type="disjunctive_pattern"/>
        <block type="conjunctive_pattern_multiple"/>
        <block type="disjunctive_pattern_multiple"/>
        <block type="multiple_identifier"/>
        <block type="underscore"/>
    </category>
    <sep></sep>
    <category name="Examples">
        <block type="theorem">
            <field name="VAR">conjunction_is_commutative</field>
            <value name="PROPOSITION">
                <block type="forall">
                    <mutation binderCount="0" />
                    <value name="BINDER0">
                        <block type="binder">
                            <mutation options="[[&quot;Prop&quot;,&quot;Prop&quot;],[&quot;nat&quot;,&quot;nat&quot;],[&quot;bool&quot;,&quot;bool&quot;],[&quot;Type&quot;,&quot;Type&quot;]]" varCount="2" typeCount="1" />
                            <field name="VAR0">P</field>
                            <field name="VAR1">Q</field>
                            <field name="TYPE0">Prop</field>
                        </block>
                    </value>
                    <value name="PROPOSITION">
                        <block type="implies">
                            <value name="LEFT">
                                <block type="conjunction_disjunction">
                                    <field name="OPERATOR">/\\</field>
                                    <value name="LEFT">
                                        <block type="variable_dropdown">
                                            <mutation options="[[&quot;P&quot;,&quot;P&quot;],[&quot;Q&quot;,&quot;Q&quot;]]" />
                                            <field name="VAR">P</field>
                                        </block>
                                    </value>
                                    <value name="RIGHT">
                                        <block type="variable_dropdown">
                                            <mutation options="[[&quot;P&quot;,&quot;P&quot;],[&quot;Q&quot;,&quot;Q&quot;]]" />
                                            <field name="VAR">Q</field>
                                        </block>
                                    </value>
                                </block>
                            </value>
                            <value name="RIGHT">
                                <block type="conjunction_disjunction">
                                    <field name="OPERATOR">/\\</field>
                                    <value name="LEFT">
                                        <block type="variable_dropdown">
                                            <mutation options="[[&quot;P&quot;,&quot;P&quot;],[&quot;Q&quot;,&quot;Q&quot;]]" />
                                            <field name="VAR">Q</field>
                                        </block>
                                    </value>
                                    <value name="RIGHT">
                                        <block type="variable_dropdown">
                                            <mutation options="[[&quot;P&quot;,&quot;P&quot;],[&quot;Q&quot;,&quot;Q&quot;]]" />
                                            <field name="VAR">P</field>
                                        </block>
                                    </value>
                                </block>
                            </value>
                        </block>
                    </value>
                </block>
            </value>
            <next>
                <block type="proof">
                    <statement name="STATEMENTS">
                        <block type="intro">
                            <field name="VAR">P</field>
                            <next>
                                <block type="intro">
                                    <field name="VAR">Q</field>
                                    <next>
                                        <block type="intro">
                                            <field name="VAR">H_P_and_Q</field>
                                            <next>
                                                <block type="destruct">
                                                    <mutation options="[[&quot;P&quot;,&quot;P&quot;],[&quot;Q&quot;,&quot;Q&quot;],[&quot;H_P_and_Q&quot;,&quot;H_P_and_Q&quot;]]" branchCount="0" />
                                                    <field name="VAR">H_P_and_Q</field>
                                                    <value name="PATTERN">
                                                        <block type="conjunctive_pattern">
                                                            <value name="LEFT">
                                                                <block type="intro_pattern_identifier">
                                                                    <field name="VAR">H_P</field>
                                                                </block>
                                                            </value>
                                                            <value name="RIGHT">
                                                                <block type="intro_pattern_identifier">
                                                                    <field name="VAR">H_Q</field>
                                                                </block>
                                                            </value>
                                                        </block>
                                                    </value>
                                                    <next>
                                                        <block type="split">
                                                            <statement name="STATEMENTS_LEFT">
                                                                <block type="exact">
                                                                    <value name="VAR">
                                                                        <block type="variable_dropdown">
                                                                            <mutation options="[[&quot;P&quot;,&quot;P&quot;],[&quot;Q&quot;,&quot;Q&quot;],[&quot;H_P&quot;,&quot;H_P&quot;],[&quot;H_Q&quot;,&quot;H_Q&quot;]]" />
                                                                            <field name="VAR">H_Q</field>
                                                                        </block>
                                                                        <shadow type="variable_dropdown" />
                                                                    </value>
                                                                </block>
                                                            </statement>
                                                            <statement name="STATEMENTS_RIGHT">
                                                                <block type="exact">
                                                                    <value name="VAR">
                                                                        <block type="variable_dropdown">
                                                                            <mutation options="[[&quot;P&quot;,&quot;P&quot;],[&quot;Q&quot;,&quot;Q&quot;],[&quot;H_P&quot;,&quot;H_P&quot;],[&quot;H_Q&quot;,&quot;H_Q&quot;]]" />
                                                                            <field name="VAR">H_P</field>
                                                                        </block>
                                                                        <shadow type="variable_dropdown" />
                                                                    </value>
                                                                </block>
                                                            </statement>
                                                        </block>
                                                    </next>
                                                </block>
                                            </next>
                                        </block>
                                    </next>
                                </block>
                            </next>
                        </block>
                    </statement>
                </block>
            </next>
        </block>
    </category>
    <category name="Challenges">
    <block type="theorem">
            <field name="VAR">conjunction_is_commutative</field>
            <value name="PROPOSITION">
                <block type="forall">
                    <mutation binderCount="0" />
                    <value name="BINDER0">
                        <block type="binder">
                            <mutation options="[[&quot;Prop&quot;,&quot;Prop&quot;],[&quot;nat&quot;,&quot;nat&quot;],[&quot;bool&quot;,&quot;bool&quot;],[&quot;Type&quot;,&quot;Type&quot;]]" varCount="2" typeCount="1" />
                            <field name="VAR0">P</field>
                            <field name="VAR1">Q</field>
                            <field name="TYPE0">Prop</field>
                        </block>
                    </value>
                    <value name="PROPOSITION">
                        <block type="implies">
                            <value name="LEFT">
                                <block type="conjunction_disjunction">
                                    <field name="OPERATOR">/\\</field>
                                    <value name="LEFT">
                                        <block type="variable_dropdown">
                                            <mutation options="[[&quot;P&quot;,&quot;P&quot;],[&quot;Q&quot;,&quot;Q&quot;]]" />
                                            <field name="VAR">P</field>
                                        </block>
                                    </value>
                                    <value name="RIGHT">
                                        <block type="variable_dropdown">
                                            <mutation options="[[&quot;P&quot;,&quot;P&quot;],[&quot;Q&quot;,&quot;Q&quot;]]" />
                                            <field name="VAR">Q</field>
                                        </block>
                                    </value>
                                </block>
                            </value>
                            <value name="RIGHT">
                                <block type="conjunction_disjunction">
                                    <field name="OPERATOR">/\\</field>
                                    <value name="LEFT">
                                        <block type="variable_dropdown">
                                            <mutation options="[[&quot;P&quot;,&quot;P&quot;],[&quot;Q&quot;,&quot;Q&quot;]]" />
                                            <field name="VAR">Q</field>
                                        </block>
                                    </value>
                                    <value name="RIGHT">
                                        <block type="variable_dropdown">
                                            <mutation options="[[&quot;P&quot;,&quot;P&quot;],[&quot;Q&quot;,&quot;Q&quot;]]" />
                                            <field name="VAR">P</field>
                                        </block>
                                    </value>
                                </block>
                            </value>
                        </block>
                    </value>
                </block>
            </value>
            <next>
                <block type="proof" />
            </next>
        </block>
        
            <block type="theorem">
            <field name="VAR">disjunction_is_commutative</field>
            <value name="PROPOSITION">
                <block type="forall">
                    <mutation binderCount="0" />
                    <value name="BINDER0">
                        <block type="binder">
                            <mutation options="[[&quot;Prop&quot;,&quot;Prop&quot;],[&quot;nat&quot;,&quot;nat&quot;],[&quot;bool&quot;,&quot;bool&quot;],[&quot;Type&quot;,&quot;Type&quot;]]" varCount="2" typeCount="1" />
                            <field name="VAR0">P</field>
                            <field name="VAR1">Q</field>
                            <field name="TYPE0">Prop</field>
                        </block>
                    </value>
                    <value name="PROPOSITION">
                        <block type="implies">
                            <value name="LEFT">
                                <block type="conjunction_disjunction">
                                    <field name="OPERATOR">\\/</field>
                                    <value name="LEFT">
                                        <block type="variable_dropdown">
                                            <mutation options="[[&quot;P&quot;,&quot;P&quot;],[&quot;Q&quot;,&quot;Q&quot;]]" />
                                            <field name="VAR">P</field>
                                        </block>
                                    </value>
                                    <value name="RIGHT">
                                        <block type="variable_dropdown">
                                            <mutation options="[[&quot;P&quot;,&quot;P&quot;],[&quot;Q&quot;,&quot;Q&quot;]]" />
                                            <field name="VAR">Q</field>
                                        </block>
                                    </value>
                                </block>
                            </value>
                            <value name="RIGHT">
                                <block type="conjunction_disjunction">
                                    <field name="OPERATOR">\\/</field>
                                    <value name="LEFT">
                                        <block type="variable_dropdown">
                                            <mutation options="[[&quot;P&quot;,&quot;P&quot;],[&quot;Q&quot;,&quot;Q&quot;]]" />
                                            <field name="VAR">Q</field>
                                        </block>
                                    </value>
                                    <value name="RIGHT">
                                        <block type="variable_dropdown">
                                            <mutation options="[[&quot;P&quot;,&quot;P&quot;],[&quot;Q&quot;,&quot;Q&quot;]]" />
                                            <field name="VAR">P</field>
                                        </block>
                                    </value>
                                </block>
                            </value>
                        </block>
                    </value>
                </block>
            </value>
            <next>
                <block type="proof" />
            </next>
        </block>
    </category>
    <!-- <button text="Create variable..." callbackKey="CREATE_VARIABLE"></button> -->
    <!-- <category name="Variables" categorystyle="variable_category" custom="VARIABLE"> -->
    <!-- </category> -->
</xml>
`

// Use this to get the XML of the current blocks on the workspace.
// console.log(Blockly.Xml.workspaceToDom(Blockly.mainWorkspace));

