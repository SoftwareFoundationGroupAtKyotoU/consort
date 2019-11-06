<html>
<head>
<title>ConSORT: Context- and Flow-Sensitive Ownership Refinement Types</title>
<meta http-equiv="Content-Type" content="text/html; charset=UTF-8">
<meta name="viewport" content="width=device-width, initial-scale=1.0">
<link rel="stylesheet" href="http://yui.yahooapis.com/pure/0.6.0/pure-min.css">
<link href='https://fonts.googleapis.com/css?family=Source+Sans+Pro:400,700|Inconsolata:400,700' rel='stylesheet' type='text/css'>
<link rel="stylesheet" href="typebase.css">
<link rel="stylesheet" href="custom.css">
<link rel="stylesheet" href="colorful.css">
</head>
<body>
<div id="content" markdown="1">
# ConSORT: Context- and Flow-Sensitive Ownership Refinement Types
{:.no_toc}

This is the project website for the ConSORT project. It provides the source code for ConSORT, its experiments, and basic instructions
for building and running.

### Table of Contents
{:.no_toc}
* Contents
{:toc}

## Source Code

The source code for ConSORT is available [here](consort.tar.bz2). The MD5 hash of the archive is `HASH_OF_ARCHIVE`.

## Building

### System Requirements

ConSORT is known to build and run on Linux. It has been successfully built under **32-bit** Cygwin on Windows (**64-bit** Cygwin does _not_ work).
Mac remains untested.

### Dependencies

At the time of writing, ConSORT requires at least OCaml 4.08 and is known to work with this version. It also depends on the following
OCaml packages (known, working OPAM versions show in parentheses):

* `menhir` (20190626)
* `ppx_sexp_conv` (v0.12.0)
* `ppx_let` (v0.12.0)
* `ppxlib` (0.8.1)
* `sexplib` (v0.12.0)

Additionally, ConSORT uses [dune](https://github.com/ocaml/dune/) for compilation. Version 1.11.3 is known to work. We also use `make` as a wrapper
to invoke dune.

### Compilation

`cd` into the extracted archive and run `make`.

## Running

### Environment

In general, ConSORT requires that the depended upon CHC solvers exist
somewhere in your path. Accordingly, ensure that at least one of [Z3](https://github.com/Z3Prover/z3/), [HoICE](https://github.com/hopv/hoice/), or
[Eldarica](https://github.com/uuverifiers/eldarica)
are available in your path. (The executable used for invoking a solver
can be overridden with command line options; see the help output of ConSORT for details.)

### Invocation

To run ConSORT, we recommend using the `test.sh` script available in source directory; this script
automatically includes the definitions of arithmetic and boolean primitives when invoking ConSORT.
ConSORT can be invoked directly with `build/_default/test.exe` from the source directory. The basic
invocation is:

```
./test.sh test-program.imp
```

`test-program.imp` is the path to some file written in our extended IMP language.

### Additional Options

All available command line options are described by passing the
`-help` flag to either `test.sh` or the underlying executable. The most important
flag is likely `-timeout`, which takes an integer argument which indicates the timeout in seconds
for the solver.

### Interpreting the Output

After invoking the solver, ConSORT will generally return one of 4 outputs:

* `VERIFIED`: indicating the program was safe
* `UNVERIFIED (unsafe)`: indicating the program is unsafe
* `UNVERIFIED (ownership)`: indicating the program could not be assigned ownership types (you may need alias annotations)
* `UNVERIFIED (timeout)`: ConSORT hit the preconfigured solving timeout (see above)

Currently ConSORT does not produce explanatory output giving, e.g., concrete counter-examples to safety.

## Running the Experiments

Our implementations of the benchmarks mentioned in the paper are
available under the `benchmarks/` folder. `jayhorn/` contains the
implementations of the JayHorn benchmarks, and `consort/` contains the
implementations of our custom benchmark suite.

To run ConSORT on our experiments, run

```
./test.sh -solver parallel -timeout 60 path/to/prog.imp
```

Note that using the parallel solver requires Eldarica, HoICE, and Z3 to be installed on your system.

### Comparison with JayHorn

Due to licensing concerns, we cannot distribute JayHorn or the
benchmarks used in the LPAR '17 paper. To perform the full comparison,
you will need to download and build the JayHorn tool. The GitHub repository is [here](https://github.com/jayhorn/jayhorn/).
We used revision `b933502ae7ee8da469939e8cb45bc3b2f801fc0a` in our experiments.

After downloading and building the tool you will need to update the experiment configuration. Set the key `jayhorn` in `config.yml`
to point to the `jayhorn.jar` file produced by the JayHorn build.

In addition you will need to download the benchmarks themselves from [here](https://github.com/jayhorn/benchmarks/).
After downloading, update the key `jayhorn_bench.jayhorn_imp` with the path to the `lpar17-benchmarks/jayhorn-benchmark` subdirectory within
the repository.

Once configuration is complete, the experiments can be run by executing `python run_experiments.py results.yml`. After completion,
results.yml will contain the complete experiment results on all test files.


**Acknowledgments**: The CSS for this site was written by
[James Bornholt](https://www.cs.utexas.edu/~bornholt/) for the
[Synapse artifact site](http://synapse.uwplse.org/popl16-aec/) and is used with permission.

</div>
</body>
</html>
