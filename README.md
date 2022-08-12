# HenBlocks

More information about HenBlocks at [bboey.com/henblocks](https://bboey.com/henblocks).

## Directory

The main files that might be of interest are:
- `core.js`
- `index.html` and `index.js`
- `custom_blocks.js` and `mutators.js`
```
├── blockly-8.0.0: Blockly library.
├── hen_blocks
│   ├── coq_generator.js: Code that generates Coq code based on the blocks.
│   ├── core.js: Contains the core algorithm that implements structured editing techniques (e.g. variable dropdowns, automatic renaming).
│   ├── custom_blocks.js: Defines the custom Blockly blocks.
│   ├── field_minus.js: External file, defines the "minus" button.
│   ├── field_plus.js: External file, defines the "plus" button.
│   ├── mutators.js: Defines advanced custom Blockly blocks which use mutators.
│   └── toolbox.js: XML that defines the Blockly toolbox.
├── index.html: Frontend. Contains entry point to the web app.
├── index.js: Contains functions that concern the frontend.
└── node_modules: Contains jsCoq npm package.
```
Note: `node_modules` is committed to the repository to allow GitHub Pages to render the web app as a static page.

## Contact
bernard [at] u.yale-nus.edu.sg
