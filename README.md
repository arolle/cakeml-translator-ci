# Building CakeML translation stack with CI caching

This examplifies how to build the CakeML stack for translation without in-logic compilation.
Functions defined in the theory [`listrevTheory`](listrevScript.sml) get translated in [`listrevProgTheory`](listrevProgScript.sml) to an s-expression.
The [`Makefile`](Makefile) compiles the previous into an executable program and runs simple tests.

A continuous integration (CI) performs these steps and finally produces the s-expression as a release artefact.
The CI leverages the [nix package manager](https://nixos.org) so that compilation of both HOL4 and CakeML is a function of a git commit.
The outputs are cached, and reused supposedly as long as the respective compilation function in `flake.nix` and its call arguments remain unchanged.

- [`flake.nix`](flake.nix) defines three compilation functions (hol4, cakeml, cakemlbin) and their commit hash input arguments.
- [`Makefile`](Makefile) defines how the code of this repository shall be compiled, and is run by `make` with `HOLDIR`, `CAKEMLDIR` and `CAKEDIR` environment variables.
- [`.github/workflows/nix.yml`](.github/workflows/nix.yml) defines the Github action workflow with caching and releasing an s-expression.

