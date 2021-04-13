# Table of Contents

- [Playing with Coq-HoTT in the browser](#playing-with-coq-hott-in-the-browser)
- [Installation instructions for Coq/HoTT](#installation-instructions-for-coq-hott)
    + [Testing](#testing)
  * [Alternative IDEs](#alternative-ides)
    + [Emacs](#emacs)
    + [VSCode](#vscode)
  * [Installation from `opam`](#installation-from--opam)

# Playing with Coq-HoTT in the browser

If you'd rather avoid installing Coq locally, you can run Coq with the 
HoTT library directly [in your browser](https://hott.github.io/EPIT-2020/jscoq-hott/).
The document there provides an introduction to Coq and jsCoq, and there is a scratchpad
with local storage in your browser that can be used to do the exercises.
You can use Ctrl-Shift-S (Cmd-Shift-S on Macs) in the scratchpad to save the file locally 
or share it through hastebin.

# Installation instructions for Coq/HoTT

To install Coq along with the Coq HoTT library, you can use pre-built packages 
for various platforms:

  - For Windows: [32 bits](https://github.com/HoTT/EPIT-2020/releases/download/v0.1/Windows.installer.32.bits.zip) and [64 bits](https://github.com/HoTT/EPIT-2020/releases/download/v0.1/Windows.installer.64.bits.zip).

  - For [MacOS](https://github.com/HoTT/EPIT-2020/releases/download/v0.1/Macos.installer.zip)
  
    Note: after copying the application to /Applications, you may have to right-click on it 
    and "Open" it explicitly to bypass MacOS's safeguard about applications downloaded from the web.

  - For Linux distributions: a [snap](https://github.com/HoTT/EPIT-2020/releases/download/v0.1/Snap.package.zip) package is available.
    To make Emacs/ProofGeneral work smoothly, you might need to add `/snap/bin` to your `PATH` environment 
    variable if not already done, and `ln -s /snap/bin/coq-prover.coqtop /snap/bin/coqtop` and 
    `ln -s /snap/bin/coq-prover.coqidetop /snap/bin/coqidetop` or point your interface to these 
    executables (`coqtop` for Emacs/ProofGeneral, `coqidetop` for VSCode). 
    You can also simply run `/snap/bin/coq-prover.coqide`.
  
These packages come with an Integrated Development Environment, CoqIDE for short,
which needs to be configured to call Coq with specific arguments. This can be done
simply by putting the following [_CoqProject](_CoqProject) file at the root of your
project, so that interfaces (CoqIDE, Emacs or VSCoq) can pick it up.

These are stripped-down (much smaller) versions of the Coq Platform, with only support for the HoTT library.
For a full Coq installation including HoTT, see [this](https://github.com/coq/platform/releases/tag/2021.02.1)
relase of the [Coq Platform](https://github.com/coq/platform).

### Testing

To test your installation, simply run the [test](TestHoTT.v) file available in this repository,
by copying it *in the same folder as _CoqProject*, opening it in `CoqIDE`, then using the forward navigation buttons to evaluate it.

## Alternative IDEs

### Emacs

If you would rather use Emacs, then you should install [Proof-General](https://proofgeneral.github.io/) 
(and the excellent `company-coq` mode) through `melpa` (look at Proof-General's page for instructions). 
If you want to customize the arguments yourself, you can use `M-x set-variable coq-prog-args` and enter 
the list `("-noinit" "-indices-matter")`. 

### VSCode

Coq also has a language server protocol implementation so it can be used with [VSCode](https://code.visualstudio.com/). To use it, install VSCode and the [VSCoq](https://marketplace.visualstudio.com/items?itemName=maximedenes.vscoq) extension. Clone this repository or create a new folder for the school and create a workspace 
for it (`Add folder to workspace...` and then `Save workspace as...`). 
Then you can either put  the `_CoqProject` file at the root of this workspace and open Coq files in the
workspace *or* set the arguments to `coq` explicitely by going to `Settings`, `Workspace`, search for `Coqtop: args`, select `edit in settings.json` and enter:

     "coqtop.args": [
          "-noinit", "-indices-matter"
     ]

## Installation from `opam`

If you already are an [`opam`](http://opam.ocaml.org) user, then you can simply install `coq` 
and the `coq-hott` package, available from the `released` repository of Coq (released on April 9th,
so do `opam update` if you don't see it). To get a fresh Coq switch with the HoTT library, simply
use:

     # opam repo add coq-released http://coq.inria.fr/opam/released
     # opam install coq.8.13.1 coq-hott.8.13

You can then use the provided `_CoqProject` file, or set the options as described above for 
the various interfaces.
