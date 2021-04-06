# Playing with Coq-HoTT in the browser

If you'd rather avoid installing Coq locally, you can run Coq with the 
HoTT library directly [in your browser](https://x80.org/rhino-hott/). 
The document there can be modified and run interactively, so that should
be enough for doing the exercises.

# Installation instructions for Coq

To install Coq along with the Coq HoTT library, you can use pre-built packages 
for various platforms:

  - For Windows: [32 bits](https://github.com/HoTT/EPIT-2020/releases/download/v0.1/Windows.installer.32.bits.zip) and [64 bits](https://github.com/HoTT/EPIT-2020/releases/download/v0.1/Windows.installer.64.bits.zip)
  - For [MacOS](https://github.com/HoTT/EPIT-2020/releases/download/v0.1/Macos.installer.zip)
  
    Note: after copying the application to /Applications, you may have to right-click on it 
    and "Open" it explicitly to bypass MacOS's safeguard about applications downloaded from the web.
  - For Linux distributions: a [snap](https://github.com/HoTT/EPIT-2020/releases/download/v0.1/Snap.package.zip) package is available.

These packages come with an Integrated Development Environment, CoqIDE for short,
which needs to be configured to call Coq with specific arguments. This can be done
simply by putting the following [_CoqProject](_CoqProject) file at the root of your
project, so that interfaces (CoqIDE, Emacs or VSCoq) can pick it up.

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
and the `coq-hott` package, available from the `extra-dev` repository of Coq, using:

     # opam repo add coq-released http://coq.inria.fr/opam/released
     # opam repo add coq-extra-dev http://coq.inria.fr/opam/extra-dev
     # opam install coq.8.13.1 coq-hott.8.13.dev

This version of the HoTT package requires to use `hoqtop` and `hoqc` in place of
the usual `coqtop` and `coqc`, you need to setup your interface accordingly.
