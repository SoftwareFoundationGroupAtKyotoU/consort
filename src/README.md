# Building

You will need the following opam packages (known working version numbers noted in parentheses):

* `menhir` (20190924)
* `ppx_sexp_conv` (v0.13.0)
* `sexplib` (v0.13.0)
* `dune` (1.11.4)
* `ppx_let` (v0.13.0)
* `ppx_custom_printf` (v0.13.0)
* `yaml` (v2.0.1)

A Makefile is also provided, but is not strictly necessary. The verification driver, `test.exe` can be built with just `dune build test.exe`.
For other targets, see the `dune` file.

The experiment test scripts require python 2.7 to run.

# Generating Intrinsic Definitions
For all but the most trivial programs, you will have to generate the intrinsic definitions, which give trusted (SMT) summaries
to the arithmetic primitive operations and comparisons. The generation script is built with `dune build genLin.exe`
and run with

`dune exec ./genLin.exe stdlib/lin.intr lin-std.smt`

This will generate the `lin.intr` and `lin-std.smt` files in the `stdlib/` directory. The format of these files is explained later.

# Requirements

At least one of the following solver executables must be installed and on your path (version numbers noted in parentheses):

* [Z3](https://github.com/Z3Prover/z3/) (4.8.4)
* [HoICE](https://github.com/hopv/hoice/) (1.8.1)
* [Eldarica](https://github.com/uuverifiers/eldarica) (2.0.1)

# Running

To run the verification tool, use the `test.sh` script included in this directory. This script will automatically include the
flags to pass the intrinsic definitions generated above to the verification driver. All arguments to the script are passed
directly through to the underlying driver executable, the `-help` flag will describe the current options.

# Code Walkthrough

There are three major components to ConSORT:

1. The language front-end and simple checker
2. Ownership inference and solving
3. Verification

Roughly speaking, the first is contained within the dune module
`lang`, the second is contained within the `ownership` module, and the
final component is found in the `consort` module (these `dune` modules are
made up of several different OCaml modules).

Components 2 and 3 rely on the shared `solving` module, which provides the infrastructure for
shelling out to an external solver tool. ConSORT does _not_ use the Z3 APIs because: a) we don't
want to tie ConSORT to any particular solver, and b) the API is _terrible_.

The problem instances sent to the solvers are represented in the [SMT-Lib 2 format](http://smtlib.cs.uiowa.edu/).
The necessary S-Expressions are generated using the `SexpPrinter` module, found in the `util` dune module.

# Flow of Verification

The entry point of the test driver is `test.ml`. It parses all command line arguments, using the argument
generators provided by the Consort module (see the code for details) and the inrinsics module.
The resulting option structure, intrinsic definitions, and provided `.imp` file are then passed to the `Consort.check_file` function.

`check_file` then executes the following sequence:

1. Lex and parse the input file (via `AstUtil.parse_file`)
2. Infer (simple) types (via `SimpleChecker.typecheck_prog`)
3. Infer ownership constraints (via `OwnershipInference.infer`)
4. Solve the ownership constraints (passing the results of step 3 to `OwnershipSolver.solve_ownership`)
  * If solving fails, verification fails
  * Otherwise, verification proceeds to step 5
5. Pass the inferred ownership values and simple types to the `FlowBackend.solve` method:
  1. The program is analyzed with `FlowInference.infer`, which generates the CHC summarizing program behavior
  2. The CHC is passed to the solver backend passed to the `FlowBackend` functor:
     * If solving suceeds with `sat`, the program is judged correct
     * If solving fails with `unsat`, the program is judge unsafe
     * If solving fails with a timeout, solver error, etc. no judgment is made

Detailed explanations of the workings of the above can be found in the corresponding module files.

# Updating the Language

You will need to update the following files:

1. (Optional) `lexer.mll`: to recognize new keywords, etc.
2. `parser.mly`: to extend the parser to recognize your new form
3. Some (potentially empty) subset the following:
  1. (Optional) `surfaceAst.ml`: to represent the surface level parse of your new form, if needed
  2. (Optional) `ast.ml`: If your new form cannot be straightforwardly represented in the low-level syntax.
  3. `simpleChecker.ml` and `astPrinter.ml`: if modifying `ast.ml`, you must update the type checker to handle the new form, and describe how to print it back.
4. If `ast.ml` was modified in the above, you must also modify `ownershipInference.ml` and `flowInference.ml` to handle the new syntactic form

# Adding a New Backend

If you want to add a new solver backend, you must make the following changes:

1. Implement the solver in a new OCaml module; update the `consort` dune module as necessary.
  * At the very least, your new module should provide a function (preferably called `solve`) which has the following type:
  ```
  opts:Solver.options ->
  debug_cons:bool ->
  ?save_cons:string ->
  get_model:bool -> defn_file:string option -> SexpPrinter.t -> Solver.result
  ```
  
  * If you want your solver to be run with the parallel backend, you must also provide a function called `solve_cont` with the following type `opts:Solver.options -> get_model:bool -> defn_file:(string option) -> SexpPrinter.t -> Solver.cont`
2. Add an argument flag for selecting the new solver. Extend the `solver` type defined in the `Consort.Options` with a descriptive variant, and extend the definition of `solver_arg_gen` in the same module.
3. Extend the pattern match in `check_file` to handle your new variant, returning a reference to the `solve` function you wrote in 1.
4. (Optional) If your solver is to be used with the parallel backend, extend the `backends` list in `parallelBackend.ml`, placing your packed module into the list.

# Syntax Extensions

The `%lm`, `%lq`, and `%m` syntax extensions are for monadic operations, and are explained in `std.ml`. They are implemented
in the `with_monad` rewriter, see that folder for the implementation. The `[%cast: t]` extension
is implemented by the `ppx_cast` rewriter, and is just replaced with `(fun x -> (x :> t))`.
