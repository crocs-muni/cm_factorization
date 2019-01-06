# CM-based factorization
Complex multiplication based factorization.
This repository contains proof of concept factorization code and scripts used in experiments.

## Proof of concept script usage

Generating CM primes:

```bash
sage cm_factor.sage --action generate --prime-bits 64
16344322632527439553
```

CM factorization:

```bash
sage cm_factor.sage -N 158697752795669080171615843390068686677 -D 11
Factorization of N: 158697752795669080171615843390068686677 is: 
14793660019451035033 * 10727416514034371869
```

## Advanced usage script

More complex script that was used to run experiments covered in the paper is `experiments.sage`.
It covers distributed computation of the factorization, class number sampling, batch BCD computation, 
Hilbert polynomial generation, primorial D computation, benchmarking.


## Dependencies

Sage 8 is required. Included packages `coloredlogs`, `humanfriendly` are optional.

