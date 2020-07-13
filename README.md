# Experiments with Generic Search using Delimited Control (ICFP 2020 Artifact)

Name:    **Effects for Efficiency: Asymptotic Speedup with Delimited Control**

Authors: **Daniel Hillerström, Sam Lindley, and John Longley**

Paper: [https://arxiv.org/abs/2007.00605](https://arxiv.org/abs/2007.00605)

## Artifact Instructions

The provided artifact contains the source files along with the raw and
processed data for the experiments reported in Section 8 of the
paper. The experiments were conducted on a Intel Xeon CPU E5-1620 v2 @
3.70GHz powered workstation running Ubuntu 16.04 LTS using [SML/NJ
v110.97 64-bit](https://www.smlnj.org/dist/working/110.97/index.html)
and [MLton
20180207](https://github.com/MLton/mlton/releases/tag/on-20180207-release)
both with factory settings.

### Directory structure

* `src/` contains the SML source files for the `n`-Queens and
  integration benchmarks.
* `raw-data/` contains the data generated by running the experiments
  on our reference machine.
* `data/` contains the processed data. The data has been processed
  using LibreOffice Calc.

### Sources

The file `src/bench.sml` contains some auxiliary functions for
configuring and running the benchmarks. The files
`src/platform_{mlton,smlnj}.sml` provide compatibility interfaces to
account for the differences in the `Cont` and `GC` modules between
SML/NJ and MLton. The file `src/mlton_driver.sml` provides the main
entry point for the benchmarks compiled with the MLton. The file
`src/catchcont.sml` contains the implementation of John Longley's
`catch-with-continue` delimited control operator which we use to in
place of an effect handler. The file `src/genericSearch.sml` contains
the implementations of the generic search procedures used in the
`n`-Queens benchmarks:

* `NaiveSearch` is the search procedure referred to as "Naïve" in the
  paper.
* `FunSearch` is the search procedure referred to as "Berger" in the
  paper.
* `ModSearch` is the search procedure referred to as "Pruned" in the
  paper.
* `CcSearch` is the search procedure referred to as "Effectful" in the
  paper.

In addition the `n`-Queens benchmark file `src/queens.ml` contains a
bespoke implementation.

The `queens.cm` and `integration.cm` files are compilation manager
files used by the SML/NJ compiler to build the benchmarks, whilst
`queens.mlb` and `integration.mlb` are ML basis files used by the
MLton compiler to build the benchmarks.

#### Queens benchmarks

The file `src/queens.sml` contains source code for the `n`-Queens
benchmarks. There are two predicates:
* `nQueens`: This predicate does not refrain from querying the
   proposed solution p repeatedly on the same argument `i`.  E.g. `(p
   0)` is evaluated afresh for each comparison with some `(p i)`,
   `i>0`.
* `nQueens'`: This remembers results of earlier queries to `p`, and in
   fact asks for each of `p 0`, `p 1`, etc once only, in this order.

#### Integration benchmarks

The file `src/integration.sml` contains the source code for the
integration benchmarks.

### Benchmark execution

SML/NJ and MLton compilers are required in order to build and run the
benchmark suite. To build the benchmark programs navigate to the
`src/` directory and type

```shell
$ make
```

As a result of the above command the following binary files should be
produced: `queens.mlton`, `integration.mlton`, `queens.amd64-linux`,
and `integration.amd64-linux`. The first two are the binaries produced
by MLton and the last two are the binaries produced by SML/NJ's
compilation manager which suffixes the target binaries with a
platform-identifier. Thus if you are using a platform other than amd64
Linux then the target binaries will have different suffixes.

To run either of the MLton binaries type
```
$ ./queens.mlton
$ ./integration.mlton
```

To run either of the SML/NJ type (replace the suffix `amd64-linux` with
the identifier for your platform)

```
$ sml @SMLload queens.amd64-linux
$ sml @SMLload integration.amd64-linux
```

We provide a simple script to run all benchmarks, simply type

```
$ ./run_all
```

If your SML/NJ installation is not amd64 or x86 Linux then you will have to
modify lines 4-21 in `run_all` such that the filenames have the proper
suffixes.

Note that every benchmark program has exponential time complexity, so
you may want to go brew more than one coffee whilst you wait for them
to finish. The expected run-time with the paper configuration is
roughly ½-1 day.

### Raw data

The `run_all` script produce as output ten CSV files containing timing
and validation information:

* integration-id-sml{nj}.csv: results for integrating the identity function.
* integration-logistic-sml{nj}.csv: results for integrating a logistic map.
* integration-square-sml{nj}.csv: results for integrating a squaring function.
* queens-find-all-sml{nj}.csv: results for finding all solutions to a `n`-Queens problem.
* queens-find-one-sml{nj}.csv: results for finding the first solution to a `n`-Queens problem.

The files with suffix `smlnj.csv` contain the data obtained by running
the corresponding benchmarks compiled with SML/NJ, whilst the
`sml.csv` suffixed files contain the data from the benchmarks compiled
with MLton.

Copies of these files produced on our reference machine are present in
`raw-data/`. Each CSV file contains five columns:
* `label`: the name of the particular generic search implementation.
* `iter`: the iteration number.
* `n`: the benchmark parameter.
* `elapsed`: the elapsed time in measured in microseconds.
* `valid`: a boolean value indicating whether the run executed
  successfully.

### Processed data

The spreadsheet `data/results.ods` contains the processed data. It
contains five sheets, one for each benchmark CSV log. The spreadsheet
is a superset of the results presented in the paper. This spreadsheet
was produced using LibreOffice Calc, but should be possible to import
into either Google Sheets or Microsoft Excel.

The spreadsheet computes two things for each generic search
implementation: the median runtime and its relative median speed-up
compared to the effectful implementation.

Description of labels and results in the five sheets:
* QueensFindAllSML{NJ} and QueensFindOneSML{NJ}: These sheets contain
  the results for both `nQueens` and `nQueens'` predicates. The results
  for `nQueens'` are the ones reported in the paper.
  + The label "Naive" corresponds to the `NaiveSearch` implementation
    in `src/genericSearch.sml` applied to the `nQueens` predicate in
    `src/queens.sml`, whilst the label "Naive'" is the same procedure
    but applied to `nQueens'`. Note "Naive" and "Naive'" are not run
    for problem sizes `n > 8` because they run too slow. Only results
    for "Naive'" are presented in the paper and the implementation is
    referred to as Naïve.
  + The label "Berger" corresponds to the `FunSearch` implementation in
    `src/genericSearch.sml` applied to the `nQueens` predicate in
    `src/queens.sml`, whilst the label "Berger'" is the same procedure
    but applied to `nQueens'`. Only the results for "Berger'" are
    presented in the paper and the implementation is referred to as
    Berger.
  + The label "Pruned" corresponds to the `ModSearch` implementation in
    `src/genericSearch.sml` applied to the `nQueens` predicate in
    `src/queens.sml`, whilst the label "Pruned'" is the same procedure
    but applied to `nQueens'`. Only the results for "Pruned'" are
    presented in the paper and the implementation is referred to as
    pruned.
  + The label "Effectful" corresponds to the `CcSearch` implementation in
    `src/genericSearch.sml` applied to the `nQueens` predicate in
    `src/queens.sml`, whilst the label "Effectful'" is the same procedure but
    applied to `nQueens'`.
  + The label "Bespoke" corresponds to the `BespokeQueens` implementation
    in `src/queens.sml`.
* IntegrationIdentitySML{NJ}, IntegrationSquareSML{NJ},
  IntegrationLogisticSML{NJ}: these sheets contain the results for
  integrating the identity function, squaring function, and logistic
  map respectively.
  + The label "Naive" corresponds to the `slowFunIntegrate01`
    function in `src/integration.sml`.
  + The label "Berger" corresponds to the function `funIntegrate01` in
    `src/integration.sml`.
  + The label "Pruned" corresponds to the function `modIntegrate01` in
    `src/integration.sml`.
  + The label "Effectful" corresponds to the function `ccIntegrate01` in
    `src/integration.sml`.
* MLton SMLNJ comparison: This sheet contains the data for Table 3 in
  the paper. The sheet computes the relative runtimes for each
  implementation.

Shield: [![CC BY 4.0][cc-by-shield]][cc-by]

This work is licensed under a
[Creative Commons Attribution 4.0 International License][cc-by].

[![CC BY 4.0][cc-by-image]][cc-by]

[cc-by]: http://creativecommons.org/licenses/by/4.0/
[cc-by-image]: https://i.creativecommons.org/l/by/4.0/88x31.png
[cc-by-shield]: https://img.shields.io/badge/License-CC%20BY%204.0-lightgrey.svg
