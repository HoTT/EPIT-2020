# Playing with Coq-HoTT in the browser

If you'd rather avoid installing Coq locally, you can run Coq with the 
HoTT library directly [in your browser](https://x80.org/rhino-hott/). 
The document there can be modified and run interactively, so that should
be enough for doing the exercises.

# Installation instructions for Coq

The Coq HoTT library requires a bit of a customized installation of Coq.
You can download pre-built packages for various platforms by following the links here:

  - For Windows: [32 bits]() and [64 bits]()
  - For [MacOS]()
  - For Linux distributions: a [snap]() package is available.

These packages come with an Integrated Development Environment, CoqIDE for short,
which needs to be configured to call a specific Coq version. To do so, simply go 
to the `Preferences` menu, under `Edit`, then the `External` tab, and set
`coqidetop` to:
    
  - On MacOS: `/Applications/Coq_Platform_2021.02.0-hott.app/Contents/Resources/bin/hoqidetop` 
  - On Windows: `C:\Coq\bin\hoqidetop`
  - On Linux: `/snap/bin/coq.hoqidetop` or `~/.opam/_coq-platform_.2021-02.0-hott/bin/hoqidetop` (for a local `opam` installation of the platform)

To test your installation, simply run the [test](TestHoTT.v) file available in this repository,
by opening the file or copy-pasting its contents in a buffer, then using the forward navigation 
buttons to evaluate it.

## Alternative IDEs

### Emacs

If you would rather use Emacs, then you should install [Proof-General](https://proofgeneral.github.io/) 
(and the excellent `company-coq` mode) through `melpa` (look at Proof-General's page for instructions). 
Then you can point to a specific `coqtop` using `M-x set-variable coq-prog-name` and enter the 
path to `hoqtop` (note, without `ide`).

### VSCode

Coq also has a language server protocol implementation so it can be used with [VSCode](https://code.visualstudio.com/). To use it, install VSCode and the [VSCoq](https://marketplace.visualstudio.com/items?itemName=maximedenes.vscoq) extension. Make a workspace for the school and set the settings as:

    "Coqtop: bin path"
         /Applications/Coq_Platform_2021.02.0.app/Contents/Resources/bin" 
         (depending on your platform installation)

    "Coqtop: Coqidetop exe"
         "hoqidetop"
    
    "Coqtop: Coqtop exe"
         "hoqtop"
    
Alternatively, you can edit the workspace file's `settings` section:

    "coqtop.binPath": "/Applications/Coq_Platform_2021.02.0.app/Contents/Resources/bin",
    "coqtop.coqidetopExe": "hoqidetop",
    "coqtop.coqtopExe": "hoqtop",

## Installation from `opam`

If you already are an [`opam`](http://opam.ocaml.org) user, then you can simply install `coq` 
and the `coq-hott` package, available from the `extra-dev` repository of Coq, using:

     # opam repo add coq-extra-dev http://coq.inria.fr/opam/extra-dev
     # opam install coq.8.13.1 coq-hott.8.13.dev

You the need to adjust for the path of `hoqidetop` in the interface you choose, which you
can find after successful installation using `which hoqidetop`.
