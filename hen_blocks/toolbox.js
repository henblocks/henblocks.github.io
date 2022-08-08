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
        <block type="definition_or_fixpoint">
            <value name="BINDER0">
                <block type="binder" />
            </value>
        </block>
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
        <block type="underscore_case"/>
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
        <block type="variable_dropdown_multiple">
            <value name="VAR0">
                <block type="variable_dropdown"/>            
            </value>
        </block>
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
        <block type="variable_dropdown_multiple">
            <value name="VAR0">
                <block type="variable_dropdown"/>            
            </value>
        </block>
    </category>
    <category name="Tactics" colour="${COLOUR_TACTICS}">
        <block type="variable_dropdown"/>
        <block type="variable_dropdown_multiple">
            <value name="VAR0">
                <block type="variable_dropdown"/>            
            </value>
        </block>
        <label text="Managing Context"></label>
        <block type="intro"/>
        <block type="revert">
            <value name="VAR">
                <block type="variable_dropdown" />
            </value>
        </block>
        
        <label text="Solving Goals"></label>
        <block type="reflexivity"/>
        <block type="exact">
            <value name="VAR">
                <block type="variable_dropdown" />
            </value>
        </block>
        <block type="contradiction">
            <value name="VAR">
                <block type="variable_dropdown" />
            </value>
        </block>
        <block type="discriminate">
            <value name="VAR">
                <block type="variable_dropdown" />
            </value>
        </block>
        
        <label text="Transforming Goals/Hypotheses"></label>
        
        <block type="rewrite">
            <value name="VAR">
                <block type="variable_dropdown_multiple">
                    <value name="VAR0">
                        <block type="variable_dropdown"/>            
                    </value>
                </block>
            </value>
        </block>
        <block type="unfold">
            <value name="VAR">
                <block type="variable_dropdown" />
            </value>
        </block>
        <block type="apply">
            <value name="VAR">
                <block type="variable_dropdown" />
            </value>
        </block>
        <!-- <block type="injection"> -->
        <!--     <value name="VAR"> -->
        <!--         <block type="variable_dropdown" /> -->
        <!--     </value> -->
        <!-- </block> -->
        <block type="symmetry"/>
        <block type="simpl"/>
        <!-- <block type="f_equal"/> -->
        
        <label text="Breaking Apart Conjunctions in Goals"></label>
        <block type="split"/>
        
        <label text="Breaking Apart Disjunctions in Goals"></label>
        <block type="left_right"/>
        
        <label text="Breaking Apart Conjunctions in Hypotheses"></label>
        <block type="destruct">
            <mutation branchCount="0" />
            <field name="COMMAND">destruct</field>
            <field name="VAR">[Select variable]</field>
            <value name="PATTERN">
                <block type="disjunctive_pattern_multiple">
                    <mutation branchCount="1" />
                    <value name="PATTERN0">
                        <block type="multiple_identifier">
                            <mutation varCount="2" />
                            <value name="VAR0">
                                <block type="intro_pattern_identifier">
                                    <field name="VAR">H_left</field>
                                </block>
                            </value>
                            <value name="VAR1">
                                <block type="intro_pattern_identifier">
                                    <field name="VAR">H_right</field>
                                </block>
                            </value>
                        </block>
                    </value>
                </block>
            </value>
        </block>
        <label text="Breaking Apart Disjunctions in Hypotheses"></label>
        <block type="destruct">
            <mutation branchCount="2" />
            <field name="COMMAND">destruct</field>
            <field name="VAR">[Select variable]</field>
            <value name="PATTERN">
                <block type="disjunctive_pattern_multiple">
                    <mutation branchCount="2" />
                    <value name="PATTERN0">
                        <block type="intro_pattern_identifier">
                            <field name="VAR">H_left</field>
                        </block>
                    </value>
                    <value name="PATTERN1">
                        <block type="intro_pattern_identifier">
                            <field name="VAR">H_right</field>
                        </block>
                    </value>
                </block>
            </value>
        </block>
        <label text="Breaking Apart Inductive Types in Hypotheses"></label>
        <block type="destruct">
            <mutation branchCount="2" />
            <field name="COMMAND">induction</field>
            <field name="VAR">[Select variable]</field>
            <value name="PATTERN">
                <block type="disjunctive_pattern_multiple">
                    <mutation branchCount="2" />
                    <value name="PATTERN0">
                        <block type="multiple_identifier">
                            <mutation varCount="0" />
                        </block>
                    </value>
                    <value name="PATTERN1">
                        <block type="multiple_identifier">
                            <mutation varCount="2" />
                            <value name="VAR0">
                                <block type="intro_pattern_identifier">
                                    <field name="VAR">n'</field>
                                </block>
                            </value>
                            <value name="VAR1">
                                <block type="intro_pattern_identifier">
                                    <field name="VAR">IHn'</field>
                                </block>
                            </value>
                        </block>
                    </value>
                </block>
            </value>
        </block>
        <label text="Intro Patterns"></label>
        <!-- <block type="conjunctive_pattern"> -->
        <!--     <value name="LEFT"> -->
        <!--         <block type="intro_pattern_identifier"> -->
        <!--             <field name="VAR">H_left</field> -->
        <!--         </block> -->
        <!--     </value> -->
        <!--     <value name="RIGHT"> -->
        <!--         <block type="intro_pattern_identifier"> -->
        <!--             <field name="VAR">H_right</field> -->
        <!--         </block> -->
        <!--     </value> -->
        <!-- </block> -->
        <!-- <block type="disjunctive_pattern"> -->
        <!--     <value name="LEFT"> -->
        <!--         <block type="intro_pattern_identifier"> -->
        <!--             <field name="VAR">H_left</field> -->
        <!--         </block> -->
        <!--     </value> -->
        <!--     <value name="RIGHT"> -->
        <!--         <block type="intro_pattern_identifier"> -->
        <!--             <field name="VAR">H_right</field> -->
        <!--         </block> -->
        <!--     </value> -->
        <!-- </block> -->
        <!-- <block type="disjunctive_pattern"> -->
        <!--     <value name="LEFT"> -->
        <!--         <block type="multiple_identifier"> -->
        <!--             <mutation varCount="0" /> -->
        <!--         </block> -->
        <!--     </value> -->
        <!--     <value name="RIGHT"> -->
        <!--         <block type="intro_pattern_identifier"> -->
        <!--             <field name="VAR">n'</field> -->
        <!--         </block> -->
        <!--     </value> -->
        <!-- </block> -->
        <!-- <block type="conjunctive_pattern_multiple"> -->
        <!--     <mutation branchCount="3" /> -->
        <!--     <value name="PATTERN0"> -->
        <!--         <block type="intro_pattern_identifier"> -->
        <!--             <field name="VAR">H0</field> -->
        <!--         </block> -->
        <!--     </value> -->
        <!--     <value name="PATTERN1"> -->
        <!--         <block type="intro_pattern_identifier"> -->
        <!--             <field name="VAR">H1</field> -->
        <!--         </block> -->
        <!--     </value> -->
        <!--     <value name="PATTERN2"> -->
        <!--         <block type="intro_pattern_identifier"> -->
        <!--             <field name="VAR">H2</field> -->
        <!--         </block> -->
        <!--     </value> -->
        <!-- </block> -->
        <block type="disjunctive_pattern_multiple">
            <mutation branchCount="2" />
            <value name="PATTERN0">
                <block type="intro_pattern_identifier">
                    <field name="VAR">H0</field>
                </block>
            </value>
            <value name="PATTERN1">
                <block type="intro_pattern_identifier">
                    <field name="VAR">H1</field>
                </block>
            </value>
        </block>
        <block type="disjunctive_pattern_multiple">
            <mutation branchCount="1" />
            <value name="PATTERN0">
                <block type="multiple_identifier">
                    <mutation varCount="2" />
                    <value name="VAR0">
                        <block type="intro_pattern_identifier">
                            <field name="VAR">H0</field>
                        </block>
                    </value>
                    <value name="VAR1">
                        <block type="intro_pattern_identifier">
                            <field name="VAR">H1</field>
                        </block>
                    </value>
                </block>
            </value>
        </block>
        <block type="multiple_identifier">
            <mutation varCount="2" />
            <value name="VAR0">
                <block type="intro_pattern_identifier">
                    <field name="VAR">H0</field>
                </block>
            </value>
            <value name="VAR1">
                <block type="intro_pattern_identifier">
                    <field name="VAR">H1</field>
                </block>
            </value>
        </block>
        <block type="intro_pattern_identifier"/>
        <block type="underscore_intro_pattern"/>
    </category>
    <sep></sep>
    <category name="Examples">
        <block type="theorem">
            <field name="VAR">conjunction_is_commutative</field>
            <value name="PROPOSITION">
                <block type="forall">
                    <mutation binderCount="0" />
                    <field name="COMMAND">forall</field>
                    <value name="BINDER0">
                        <block type="binder" movable="false">
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
                                            <mutation options="[[&quot;P&quot;,&quot;P&quot;],[&quot;Q&quot;,&quot;Q&quot;],[&quot;S&quot;,&quot;S&quot;],[&quot;O&quot;,&quot;O&quot;],[&quot;true&quot;,&quot;true&quot;],[&quot;false&quot;,&quot;false&quot;]]" />
                                            <field name="VAR">P</field>
                                        </block>
                                    </value>
                                    <value name="RIGHT">
                                        <block type="variable_dropdown">
                                            <mutation options="[[&quot;P&quot;,&quot;P&quot;],[&quot;Q&quot;,&quot;Q&quot;],[&quot;S&quot;,&quot;S&quot;],[&quot;O&quot;,&quot;O&quot;],[&quot;true&quot;,&quot;true&quot;],[&quot;false&quot;,&quot;false&quot;]]" />
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
                                            <mutation options="[[&quot;P&quot;,&quot;P&quot;],[&quot;Q&quot;,&quot;Q&quot;],[&quot;S&quot;,&quot;S&quot;],[&quot;O&quot;,&quot;O&quot;],[&quot;true&quot;,&quot;true&quot;],[&quot;false&quot;,&quot;false&quot;]]" />
                                            <field name="VAR">Q</field>
                                        </block>
                                    </value>
                                    <value name="RIGHT">
                                        <block type="variable_dropdown">
                                            <mutation options="[[&quot;P&quot;,&quot;P&quot;],[&quot;Q&quot;,&quot;Q&quot;],[&quot;S&quot;,&quot;S&quot;],[&quot;O&quot;,&quot;O&quot;],[&quot;true&quot;,&quot;true&quot;],[&quot;false&quot;,&quot;false&quot;]]" />
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
                                                    <field name="COMMAND">destruct</field>
                                                    <field name="VAR">H_P_and_Q</field>
                                                    <value name="PATTERN">
                                                        <block type="disjunctive_pattern_multiple">
                                                            <mutation branchCount="1" />
                                                            <value name="PATTERN0">
                                                                <block type="multiple_identifier">
                                                                    <mutation varCount="2" />
                                                                    <value name="VAR0">
                                                                        <block type="intro_pattern_identifier">
                                                                            <field name="VAR">H_P</field>
                                                                        </block>
                                                                    </value>
                                                                    <value name="VAR1">
                                                                        <block type="intro_pattern_identifier">
                                                                            <field name="VAR">H_Q</field>
                                                                        </block>
                                                                    </value>
                                                                </block>
                                                            </value>
                                                        </block>
                                                    </value>
                                                    <next>
                                                        <block type="split">
                                                            <statement name="STATEMENTS_LEFT">
                                                                <block type="exact">
                                                                    <value name="VAR">
                                                                        <shadow type="variable_dropdown">
                                                                            <mutation options="[[&quot;[Select variable]&quot;,&quot;[Select variable]&quot;]]" />
                                                                            <field name="VAR">[Select variable]</field>
                                                                        </shadow>
                                                                        <block type="variable_dropdown">
                                                                            <mutation options="[[&quot;P&quot;,&quot;P&quot;],[&quot;Q&quot;,&quot;Q&quot;],[&quot;H_P&quot;,&quot;H_P&quot;],[&quot;H_Q&quot;,&quot;H_Q&quot;]]" />
                                                                            <field name="VAR">H_Q</field>
                                                                        </block>
                                                                    </value>
                                                                </block>
                                                            </statement>
                                                            <statement name="STATEMENTS_RIGHT">
                                                                <block type="exact">
                                                                    <value name="VAR">
                                                                        <shadow type="variable_dropdown">
                                                                            <mutation options="[[&quot;[Select variable]&quot;,&quot;[Select variable]&quot;]]" />
                                                                            <field name="VAR">[Select variable]</field>
                                                                        </shadow>
                                                                        <block type="variable_dropdown">
                                                                            <mutation options="[[&quot;P&quot;,&quot;P&quot;],[&quot;Q&quot;,&quot;Q&quot;],[&quot;H_P&quot;,&quot;H_P&quot;],[&quot;H_Q&quot;,&quot;H_Q&quot;]]" />
                                                                            <field name="VAR">H_P</field>
                                                                        </block>
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
        
        <block type="inductive">
            <mutation branchCount="2" />
            <field name="VAR">nat'</field>
            <value name="BRANCH0">
                <block type="constructor_definition" movable="false">
                    <mutation binderCount="0" />
                    <field name="VAR">O'</field>
                </block>
            </value>
            <value name="BRANCH1">
                <block type="constructor_definition" movable="false">
                    <mutation binderCount="1" />
                    <field name="VAR">S'</field>
                    <value name="BINDER0">
                        <block type="binder" deletable="false" movable="false">
                            <mutation options="[[&quot;Prop&quot;,&quot;Prop&quot;],[&quot;nat&quot;,&quot;nat&quot;],[&quot;bool&quot;,&quot;bool&quot;],[&quot;Type&quot;,&quot;Type&quot;],[&quot;nat'&quot;,&quot;nat'&quot;]]" varCount="1" typeCount="1" />
                            <field name="VAR0">n'</field>
                            <field name="TYPE0">nat'</field>
                        </block>
                    </value>
                </block>
            </value>
        </block>
        
        <block type="definition_or_fixpoint">
            <mutation binderCount="1" options="[[&quot;Prop&quot;,&quot;Prop&quot;],[&quot;nat&quot;,&quot;nat&quot;],[&quot;bool&quot;,&quot;bool&quot;],[&quot;Type&quot;,&quot;Type&quot;]]" />
            <field name="COMMAND">Fixpoint</field>
            <field name="VAR">add</field>
            <field name="TYPE">nat</field>
            <value name="BINDER0">
                <block type="binder" deletable="false" movable="false">
                    <mutation options="[[&quot;Prop&quot;,&quot;Prop&quot;],[&quot;nat&quot;,&quot;nat&quot;],[&quot;bool&quot;,&quot;bool&quot;],[&quot;Type&quot;,&quot;Type&quot;]]" varCount="2" typeCount="1" />
                    <field name="VAR0">i</field>
                    <field name="VAR1">j</field>
                    <field name="TYPE0">nat</field>
                </block>
            </value>
            <value name="EXPRESSION">
                <block type="match">
                    <mutation options="[[&quot;i&quot;,&quot;i&quot;],[&quot;j&quot;,&quot;j&quot;]]" branchCount="2" />
                    <field name="VAR">i</field>
                    <value name="CASE0">
                        <shadow type="case_constructor">
                            <mutation options="[[&quot;[Select constructor]&quot;,&quot;[Select constructor]&quot;]]" argCount="0" />
                            <field name="VAR">[Select constructor]</field>
                        </shadow>
                        <block type="case_constructor">
                            <mutation options="[[&quot;S&quot;,&quot;S&quot;],[&quot;O&quot;,&quot;O&quot;],[&quot;true&quot;,&quot;true&quot;],[&quot;false&quot;,&quot;false&quot;]]" argCount="0" />
                            <field name="VAR">O</field>
                        </block>
                    </value>
                    <value name="RESULT0">
                        <block type="variable_dropdown">
                            <mutation options="[[&quot;i&quot;,&quot;i&quot;],[&quot;j&quot;,&quot;j&quot;],[&quot;add&quot;,&quot;add&quot;]]" />
                            <field name="VAR">j</field>
                        </block>
                    </value>
                    <value name="CASE1">
                        <shadow type="case_constructor">
                            <mutation options="[[&quot;[Select constructor]&quot;,&quot;[Select constructor]&quot;]]" argCount="0" />
                            <field name="VAR">[Select constructor]</field>
                        </shadow>
                        <block type="case_constructor">
                            <mutation options="[[&quot;S&quot;,&quot;S&quot;],[&quot;O&quot;,&quot;O&quot;],[&quot;true&quot;,&quot;true&quot;],[&quot;false&quot;,&quot;false&quot;]]" argCount="1" />
                            <field name="VAR">S</field>
                            <value name="ARG0">
                                <block type="case_identifier">
                                    <field name="VAR">i'</field>
                                </block>
                            </value>
                        </block>
                    </value>
                    <value name="RESULT1">
                        <block type="successor">
                            <value name="NUM">
                                <block type="variable_dropdown_multiple">
                                    <mutation extraVarCount="2" options="[[&quot;i&quot;,&quot;i&quot;],[&quot;j&quot;,&quot;j&quot;],[&quot;i'&quot;,&quot;i'&quot;],[&quot;add&quot;,&quot;add&quot;]]" />
                                    <field name="VAR">add</field>
                                    <value name="VAR0">
                                        <block type="variable_dropdown">
                                            <mutation options="[[&quot;i&quot;,&quot;i&quot;],[&quot;j&quot;,&quot;j&quot;],[&quot;i'&quot;,&quot;i'&quot;],[&quot;add&quot;,&quot;add&quot;]]" />
                                            <field name="VAR">i'</field>
                                        </block>
                                    </value>
                                    <value name="VAR1">
                                        <block type="variable_dropdown">
                                            <mutation options="[[&quot;i&quot;,&quot;i&quot;],[&quot;j&quot;,&quot;j&quot;],[&quot;i'&quot;,&quot;i'&quot;],[&quot;add&quot;,&quot;add&quot;]]" />
                                            <field name="VAR">j</field>
                                        </block>
                                    </value>
                                </block>
                            </value>
                        </block>
                    </value>
                </block>
            </value>
        </block>
        <block type="theorem">
            <field name="VAR">add_is_associative</field>
            <value name="PROPOSITION">
                <block type="forall">
                    <mutation binderCount="0" />
                    <field name="COMMAND">forall</field>
                    <value name="BINDER0">
                        <shadow type="binder">
                            <mutation options="[[&quot;Prop&quot;,&quot;Prop&quot;],[&quot;nat&quot;,&quot;nat&quot;],[&quot;bool&quot;,&quot;bool&quot;],[&quot;Type&quot;,&quot;Type&quot;]]" varCount="1" typeCount="1" />
                            <field name="VAR0">var0</field>
                            <field name="TYPE0">Prop</field>
                        </shadow>
                        <block type="binder" deletable="false" movable="false">
                            <mutation options="[[&quot;Prop&quot;,&quot;Prop&quot;],[&quot;nat&quot;,&quot;nat&quot;],[&quot;bool&quot;,&quot;bool&quot;],[&quot;Type&quot;,&quot;Type&quot;]]" varCount="3" typeCount="1" />
                            <field name="VAR0">x</field>
                            <field name="VAR1">y</field>
                            <field name="VAR2">z</field>
                            <field name="TYPE0">nat</field>
                        </block>
                    </value>
                    <value name="PROPOSITION">
                        <block type="equality">
                            <value name="LEFT">
                                <block type="variable_dropdown_multiple">
                                    <mutation extraVarCount="2" options="[[&quot;x&quot;,&quot;x&quot;],[&quot;y&quot;,&quot;y&quot;],[&quot;z&quot;,&quot;z&quot;],[&quot;add&quot;,&quot;add&quot;]]" />
                                    <field name="VAR">add</field>
                                    <value name="VAR0">
                                        <block type="variable_dropdown">
                                            <mutation options="[[&quot;x&quot;,&quot;x&quot;],[&quot;y&quot;,&quot;y&quot;],[&quot;z&quot;,&quot;z&quot;],[&quot;add&quot;,&quot;add&quot;]]" />
                                            <field name="VAR">x</field>
                                        </block>
                                    </value>
                                    <value name="VAR1">
                                        <block type="variable_dropdown_multiple">
                                            <mutation extraVarCount="2" options="[[&quot;x&quot;,&quot;x&quot;],[&quot;y&quot;,&quot;y&quot;],[&quot;z&quot;,&quot;z&quot;],[&quot;add&quot;,&quot;add&quot;]]" />
                                            <field name="VAR">add</field>
                                            <value name="VAR0">
                                                <block type="variable_dropdown">
                                                    <mutation options="[[&quot;x&quot;,&quot;x&quot;],[&quot;y&quot;,&quot;y&quot;],[&quot;z&quot;,&quot;z&quot;],[&quot;add&quot;,&quot;add&quot;]]" />
                                                    <field name="VAR">y</field>
                                                </block>
                                            </value>
                                            <value name="VAR1">
                                                <block type="variable_dropdown">
                                                    <mutation options="[[&quot;x&quot;,&quot;x&quot;],[&quot;y&quot;,&quot;y&quot;],[&quot;z&quot;,&quot;z&quot;],[&quot;add&quot;,&quot;add&quot;]]" />
                                                    <field name="VAR">z</field>
                                                </block>
                                            </value>
                                        </block>
                                    </value>
                                </block>
                            </value>
                            <value name="RIGHT">
                                <block type="variable_dropdown_multiple">
                                    <mutation extraVarCount="2" options="[[&quot;x&quot;,&quot;x&quot;],[&quot;y&quot;,&quot;y&quot;],[&quot;z&quot;,&quot;z&quot;],[&quot;add&quot;,&quot;add&quot;]]" />
                                    <field name="VAR">add</field>
                                    <value name="VAR0">
                                        <block type="variable_dropdown_multiple">
                                            <mutation extraVarCount="2" options="[[&quot;x&quot;,&quot;x&quot;],[&quot;y&quot;,&quot;y&quot;],[&quot;z&quot;,&quot;z&quot;],[&quot;add&quot;,&quot;add&quot;]]" />
                                            <field name="VAR">add</field>
                                            <value name="VAR0">
                                                <block type="variable_dropdown">
                                                    <mutation options="[[&quot;x&quot;,&quot;x&quot;],[&quot;y&quot;,&quot;y&quot;],[&quot;z&quot;,&quot;z&quot;],[&quot;add&quot;,&quot;add&quot;]]" />
                                                    <field name="VAR">x</field>
                                                </block>
                                            </value>
                                            <value name="VAR1">
                                                <block type="variable_dropdown">
                                                    <mutation options="[[&quot;x&quot;,&quot;x&quot;],[&quot;y&quot;,&quot;y&quot;],[&quot;z&quot;,&quot;z&quot;],[&quot;add&quot;,&quot;add&quot;]]" />
                                                    <field name="VAR">y</field>
                                                </block>
                                            </value>
                                        </block>
                                    </value>
                                    <value name="VAR1">
                                        <block type="variable_dropdown">
                                            <mutation options="[[&quot;x&quot;,&quot;x&quot;],[&quot;y&quot;,&quot;y&quot;],[&quot;z&quot;,&quot;z&quot;],[&quot;add&quot;,&quot;add&quot;]]" />
                                            <field name="VAR">z</field>
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
                            <field name="VAR">x</field>
                            <next>
                                <block type="intro">
                                    <field name="VAR">y</field>
                                    <next>
                                        <block type="intro">
                                            <field name="VAR">z</field>
                                            <next>
                                                <block type="destruct">
                                                    <mutation options="[[&quot;x&quot;,&quot;x&quot;],[&quot;y&quot;,&quot;y&quot;],[&quot;z&quot;,&quot;z&quot;]]" branchCount="2" />
                                                    <field name="COMMAND">induction</field>
                                                    <field name="VAR">x</field>
                                                    <value name="PATTERN">
                                                        <block type="disjunctive_pattern_multiple">
                                                            <mutation branchCount="2" />
                                                            <value name="PATTERN0">
                                                                <block type="multiple_identifier">
                                                                    <mutation varCount="0" />
                                                                </block>
                                                            </value>
                                                            <value name="PATTERN1">
                                                                <block type="multiple_identifier">
                                                                    <mutation varCount="2" />
                                                                    <value name="VAR0">
                                                                        <block type="intro_pattern_identifier">
                                                                            <field name="VAR">x'</field>
                                                                        </block>
                                                                    </value>
                                                                    <value name="VAR1">
                                                                        <block type="intro_pattern_identifier">
                                                                            <field name="VAR">IHx'</field>
                                                                        </block>
                                                                    </value>
                                                                </block>
                                                            </value>
                                                        </block>
                                                    </value>
                                                    <statement name="STATEMENTS0">
                                                        <block type="simpl">
                                                            <next>
                                                                <block type="reflexivity" />
                                                            </next>
                                                        </block>
                                                    </statement>
                                                    <statement name="STATEMENTS1">
                                                        <block type="simpl">
                                                            <next>
                                                                <block type="rewrite">
                                                                    <field name="ARROW">LTR</field>
                                                                    <value name="VAR">
                                                                        <block type="variable_dropdown">
                                                                            <mutation options="[[&quot;y&quot;,&quot;y&quot;],[&quot;z&quot;,&quot;z&quot;],[&quot;x'&quot;,&quot;x'&quot;],[&quot;IHx'&quot;,&quot;IHx'&quot;],[&quot;add&quot;,&quot;add&quot;]]" />
                                                                            <field name="VAR">IHx'</field>
                                                                        </block>
                                                                    </value>
                                                                    <next>
                                                                        <block type="reflexivity" />
                                                                    </next>
                                                                </block>
                                                            </next>
                                                        </block>
                                                    </statement>
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
            <field name="VAR">modus_ponens</field>
            <value name="PROPOSITION">
                <block type="forall">
                    <mutation binderCount="0" />
                    <field name="COMMAND">forall</field>
                    <value name="BINDER0">
                        <block type="binder" deletable="false" movable="false">
                            <mutation options="[[&quot;Prop&quot;,&quot;Prop&quot;],[&quot;nat&quot;,&quot;nat&quot;],[&quot;bool&quot;,&quot;bool&quot;],[&quot;Type&quot;,&quot;Type&quot;]]" varCount="2" typeCount="1" />
                            <field name="VAR0">P</field>
                            <field name="VAR1">Q</field>
                            <field name="TYPE0">Prop</field>
                        </block>
                    </value>
                    <value name="PROPOSITION">
                        <block type="implies">
                            <field name="OPERATOR">-&gt;</field>
                            <value name="LEFT">
                                <block type="variable_dropdown">
                                    <mutation options="[[&quot;P&quot;,&quot;P&quot;],[&quot;Q&quot;,&quot;Q&quot;]]" />
                                    <field name="VAR">P</field>
                                </block>
                            </value>
                            <value name="RIGHT">
                                <block type="implies">
                                    <field name="OPERATOR">-&gt;</field>
                                    <value name="LEFT">
                                        <block type="implies">
                                            <field name="OPERATOR">-&gt;</field>
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
                                        <block type="variable_dropdown">
                                            <mutation options="[[&quot;P&quot;,&quot;P&quot;],[&quot;Q&quot;,&quot;Q&quot;]]" />
                                            <field name="VAR">Q</field>
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
            <field name="VAR">modus_tollens</field>
            <value name="PROPOSITION">
                <block type="forall">
                    <mutation binderCount="0" />
                    <field name="COMMAND">forall</field>
                    <value name="BINDER0">
                        <block type="binder" deletable="false" movable="false">
                            <mutation options="[[&quot;Prop&quot;,&quot;Prop&quot;],[&quot;nat&quot;,&quot;nat&quot;],[&quot;bool&quot;,&quot;bool&quot;],[&quot;Type&quot;,&quot;Type&quot;]]" varCount="2" typeCount="1" />
                            <field name="VAR0">P</field>
                            <field name="VAR1">Q</field>
                            <field name="TYPE0">Prop</field>
                        </block>
                    </value>
                    <value name="PROPOSITION">
                        <block type="implies">
                            <field name="OPERATOR">-&gt;</field>
                            <value name="LEFT">
                                <block type="not">
                                    <value name="PROPOSITION">
                                        <block type="variable_dropdown">
                                            <mutation options="[[&quot;P&quot;,&quot;P&quot;],[&quot;Q&quot;,&quot;Q&quot;]]" />
                                            <field name="VAR">Q</field>
                                        </block>
                                    </value>
                                </block>
                            </value>
                            <value name="RIGHT">
                                <block type="implies">
                                    <field name="OPERATOR">-&gt;</field>
                                    <value name="LEFT">
                                        <block type="implies">
                                            <field name="OPERATOR">-&gt;</field>
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
                                        <block type="not">
                                            <value name="PROPOSITION">
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
                </block>
            </value>
            <next>
                <block type="proof" />
            </next>
        </block>
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

