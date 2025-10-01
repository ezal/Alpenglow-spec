This folder contains a specification in [Quint](https://quint-lang.org/) of the
dual-path Simplex protocol from the ["Concurrent 2-round and 3-round
Simplex-style
BFT"](https://decentralizedthoughts.github.io/2025-07-29-2-round-3-round-simplex/)
blog post.

This is a one-shot consensus protocol with integrated fast and slow paths. That
is, when assuming network synchrony and an honest leader,

* *fast path*: decision after 1 voting phase (with `n-p` votes) if at most `p` failures
* *slow path*: decision after 2 voting phases (with `n-f-p` votes) if at most `f` Byzantine failures and `p` crash failures (and `p<=f`)

The agreement property is specified and a few scenarios (with and without
Byzantines). Use `make test` to run all the specified scenarios. Use `make run`
to check the agreement property.

## Playing with the specification in Quint

To play a scenario, do for instance:
```
$ quint -r instances.qnt::simplex_2_parties
> fast_agree_in_view_0
> s
```

See `instances.qnt` for the other scenarios.

One could generate many traces using for instance:
```
quint run instances.qnt --main simplex_2_byz --invariant agreement --mbt --out-itf=traces/out.itf.json --n-traces 100
```

After any change do `make parse` and `make typecheck` to ensure no parse or typing errors are introduced.
