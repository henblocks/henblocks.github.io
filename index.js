const HENBLOCKS_VERSION = "0.1.0";

document.querySelector("#henblocks-version").innerText = ` ${HENBLOCKS_VERSION}`;

/**
 * Bernard: From Blockly Resizable demo https://github.com/google/blockly/blob/master/demos/resizable/overlay.html
 */
const blocklyArea = document.querySelector('#blocklyArea');
const blocklyDiv = document.querySelector('#blocklyDiv');
const options = {
    media: 'blockly-8.0.0/media/',
    toolbox: coqToolbox,
    // Bernard: From Blockly advanced playground template
    zoom: {
        controls: true,
        wheel: true,
        startScale: 1.0,
        maxScale: 4,
        minScale: 0.25,
        scaleSpeed: 1.1
    },
    grid: {
        spacing: 25,
        length: 3,
        colour: '#ccc',
        snap: true
    },
    // Bernard: End of Blockly advanced playground template
}
const blocklyWorkspace = Blockly.inject(blocklyDiv, options);
const onresize = function () {
    // Compute the absolute coordinates and dimensions of blocklyArea.
    let element = blocklyArea;
    let x = 0;
    let y = 0;
    do {
        x += element.offsetLeft;
        y += element.offsetTop;
        element = element.offsetParent;
    } while (element);
    // Position blocklyDiv over blocklyArea.
    blocklyDiv.style.left = x + 'px';
    blocklyDiv.style.top = y + 'px';
    blocklyDiv.style.width = blocklyArea.offsetWidth + 'px';
    blocklyDiv.style.height = blocklyArea.offsetHeight + 'px';
    Blockly.svgResize(blocklyWorkspace);
};
window.addEventListener('resize', onresize, false);
onresize();
Blockly.svgResize(blocklyWorkspace);
// End of Blockly Resizable demo


/**
 * Bernard: From jsCoq template https://github.com/jscoq/jscoq/blob/v8.14/examples/npm-template.html
 */
// jsCoq configuration part
let coqManager; // Bernard: Added to store the coq manager

const jscoq_ids = ['coq-code'];
const jscoq_opts = {
    prelude: true,
    implicit_libs: true,
    base_path: './node_modules/jscoq/',
    // Bernard: Changed company-coq to false so that forall and exists will be rendered as is and not as unicode symbols
    editor: {mode: {'company-coq': false}, keyMap: 'default', /* Added by Bernard --> */ readOnly: true},
    init_pkgs: ['init'],
    all_pkgs: ['coq']
};

const coqManagerPromise = JsCoq.start(jscoq_opts.base_path, './node_modules', jscoq_ids, jscoq_opts);
// Bernard: Added to store the CoqManager object in the variable
coqManagerPromise.then(c => {
    coqManager = c;
})

// Bernard: End of jsCoq Template

/**
 * New stuff
 */
// Must wait for page to load because must wait for code mirror to be injected
window.addEventListener('load', onload);

function onload() {
    generateAndDisplayCode();
    blocklyWorkspace.addChangeListener(generateAndDisplayCode);
}

BlocklyStorage.backupOnUnload();
blocklyWorkspace.addChangeListener(prepareToTraverseBlocks);

function restoreBlocks() {
    // Wait for Blockly to load block definitions. A TypeError is thrown if they have not yet been loaded.
    try {
        BlocklyStorage.restoreBlocks();
    } catch (e) {
        setTimeout(restoreBlocks, 10);
    }
}

restoreBlocks();

function generateAndDisplayCode() {
    // Referenced from https://stackoverflow.com/questions/8378678/how-can-i-set-the-value-of-a-codemirror-editor-using-javascript/62711689#62711689
    // To programmatically add code to codemirror editor
    const editor = document.querySelector('.CodeMirror').CodeMirror;
    // This doesn't work, because the textarea gets replaced by CodeMirror.
    // document.querySelector("#coq-code").textContent = code;

    const oldCode = editor.getValue();
    try {
        const newCode = coqGenerator.workspaceToCode(blocklyWorkspace);
        if (editor.getValue() === "Loading...") {
            editor.setValue(newCode);
        } else {
            const [i, pos] = findFirstDiffPos(oldCode, newCode);
            if (i !== null) {
                // TODO: I need to change the 10000 thing I think.
                editor.replaceRange(newCode.slice(i), pos, {line: 10000, ch: 1000}, "");
            }
        }
    } catch (e) {
        editor.setValue(`${e}`);
    }
}

// Bernard: Custom function written with inspiration from
// https://stackoverflow.com/questions/32858626/detect-position-of-first-difference-in-2-strings
function findFirstDiffPos(s1, s2) {
    if (s1 === s2) return [null, null];
    let i = 0;
    let line = 0;
    let ch = 0;
    while (s1[i] === s2[i]) {
        ch++;
        if (s1[i] === "\n") {
            line++;
            ch = 0;
        }
        i++;
    }
    return [i, {line, ch}];
}

// Bernard: Custom function to download code with inspiration from
// https://ourcodeworld.com/articles/read/189/how-to-create-a-file-and-generate-a-download-with-javascript-in-the-browser-without-a-server
function downloadFile(filename, contents) {
    const element = document.createElement("a");
    element.setAttribute("href", "data:text/plain;charset=utf-8," + encodeURIComponent(contents))
    element.setAttribute("download", filename);
    element.style.display = "none";
    document.body.appendChild(element);
    element.click();
    document.body.removeChild(element);
}

// Bernard
function getCurrentDateTimeString() {
    const dateObj = new Date();
    const year = dateObj.getFullYear();
    const month = ("0" + (dateObj.getMonth() + 1)).slice(-2);
    const date = ("0" + dateObj.getDate()).slice(-2);
    const hour = ("0" + dateObj.getHours()).slice(-2);
    const minutes = ("0" + dateObj.getMinutes()).slice(-2);
    return `${year}-${month}-${date}-${hour}-${minutes}`;
}

// Bernard
function downloadCoqCode() {
    const editor = document.querySelector('.CodeMirror').CodeMirror;
    const code = editor.getValue();

    const dateObj = new Date();
    const fileContents = `(* Coq code generated from HenBlocks v${HENBLOCKS_VERSION} (https://henblocks.github.io/) *)\n`
        + `(* ${dateObj.toDateString()} ${dateObj.toTimeString()} *)\n\n`
        + code;
    const filename = `coq-blocks-${getCurrentDateTimeString()}.v`;

    downloadFile(filename, fileContents);
}

// Bernard
function downloadBlocklyXml() {
    const dom = Blockly.Xml.workspaceToDom(Blockly.mainWorkspace);
    const xml = Blockly.Xml.domToPrettyText(dom);
    const dateObj = new Date();
    const fileContents = `<!-- XML blocks generated from HenBlocks v${HENBLOCKS_VERSION} -->\n`
        + "<!-- Visit https://henblocks.github.io/ and upload this file to see the contents -->\n"
        + `<!-- ${dateObj.toDateString()} ${dateObj.toTimeString()} -->\n\n`
        + xml;
    const filename = `coq-blocks-${getCurrentDateTimeString()}.xml`;

    downloadFile(filename, fileContents);
}

//Bernard
function openFileDialog() {
    document.querySelector("#file-input").click();
}

// Bernard
function uploadBlocklyXml(event) {
    const file = event.target.files[0];
    if (!file.type.match("xml")) {
        displayErrorToast("Error: Uploaded file is not an XML file.");
        return;
    }

    event.target.value = null;
    const reader = new FileReader();
    reader.onload = function () {
        const xml = reader.result;
        let dom;
        try {
            dom = Blockly.Xml.textToDom(xml);
        } catch (e) {
            displayErrorToast("Error parsing XML file. Please ensure the XML file was generated from this website.");
            return;
        }

        const oldNumBlocks = Blockly.mainWorkspace.getAllBlocks(false).length;
        try {
            Blockly.Xml.appendDomToWorkspace(dom, Blockly.mainWorkspace);
        } catch (e) {
            displayErrorToast("Error adding blocks to workspace. Was the XML file generated by an earlier " +
                "incompatible version? Was the XML file edited?");
            return;
        }
        const newNumBlocks = Blockly.mainWorkspace.getAllBlocks(false).length;
        displayUploadBlocklyXmlSuccessToast(newNumBlocks - oldNumBlocks);
    }
    reader.readAsText(file);


    // Referenced from https://groups.google.com/g/blockly/c/IeSzg4DQ1TM
    // if (typeof xml != "string" || xml.length < 5) {
    //     alert("No Input");
    //     return false;
    //     return;
    // }
    // try {
    //     var dom = Blockly.Xml.textToDom(xml);
    //     Blockly.mainWorkspace.clear();
    //     Blockly.Xml.domToWorkspace(Blockly.mainWorkspace, dom);
    //     return true;
    // } catch (e) {
    //     alert("Invalid xml");
    //     return false;
    // }
}

function toggleCoqPanel() {
    document.querySelector("#ide-wrapper").classList.toggle('hideCoqPanel');
    const button = document.querySelector("#toggleCoqPanelButton");
    button.innerHTML = button.innerHTML === "▶" ? "◀" : "▶";
    onresize();
}

function createToastElement(text, bgColor) {
    const toastElement = document.createElement("div");
    toastElement.innerText = text;
    toastElement.classList.add("toast", "show-toast");
    toastElement.style.backgroundColor = bgColor;
    document.body.appendChild(toastElement);
    setTimeout(function () {
        toastElement.remove();
    }, 3000);
}

function displayUploadBlocklyXmlSuccessToast(numBlocks) {
    const numBlockText = numBlocks === 1 ? "1 block has" : `${numBlocks} blocks have`;
    createToastElement(`${numBlockText} been added from the XML file.`, "green");
}

function displayErrorToast(text) {
    createToastElement(text, "red");
}
