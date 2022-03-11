# Btor2CHC
Btor2CHC is built on top of CoSA2 (now named as [Pono](https://github.com/upscale-project/pono)).

## Setup

```
git clone git@github.com:zhanghongce/cosa2.git btor2chc
cd btor2chc
git checkout -b btor2chc-v2 origin/btor2chc-v2
./contrib/setup-smt-switch.sh --with-msat
./contrib/setup-btor2tools.sh
./contrib/setup-bison.sh
./configure.sh --with-msat
cd build
make
```

And you should get a binary `cosa2` under the `build` directory.

## Usage

Btor2CHC supports both the main CHC format and the rule dialect.

* To convert Btor2 to the rule dialect that Z3 supports: `cosa2 -e chcrel --no-names -v 1 --chc output.chc input.btor`
* To convert Btor2 to the classic CHC format: `cosa2 -e chc --no-names -v 1 --chc output.chc input.btor`

The `--no-names` option is to ask Btor2CHC to mask the variable names in Btor2. We have seem some cases that Btor2 variables can have such name like `push` and it will overwhelm the CHC solver.

You can ignore the print-out of Btor2CHC like the following:
```
unknown
b0
```
As we are not using CoSA2 for any verification of the input Btor2, it does know if the property holds. That's why it has such "unknown".

## License Issue

Btor2CHC uses CoSA2 to parse Btor2 input and uses the SMT solver to generate SMT-LIB2 expressions and then assemble the SMT-LIB2 expressions into the CHC format. We have tested with MathSAT. Some solvers, e.g. Boolector, mix `Bool` and `(_ BitVec 1)`. This could be a problem as the generated CHC will not pass type check.

However, MathSAT is limited to research and evaluation purposes only. Please review the [license of MathSAT](https://mathsat.fbk.eu/download.html)

In the future, hopefully, I will port it to using CVC4.

## Other Btor2Chc Tool

You can also check the `btor2chc` tool from [chc-tools](https://github.com/chc-comp/chc-tools)

