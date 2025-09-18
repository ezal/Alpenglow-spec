This folder contains a specification in Quint of dual-path Simplex protocol from the [Concurrent 2-round and 3-round Simplex-style BFT" (Simplex](https://decentralizedthoughts.github.io/2025-07-29-2-round-3-round-simplex/) blog post.
This is a one-shot consensus protocol with integrated fast and slow paths.
* Fast path: 2 rounds with `n-p` votes when at most `p` failures
* Slow path: 3 rounds with `n-f-p` votes when at most `f` failures

For now only 3 scenarios are specified and the agreement property.

## Playing with the specification in Quint

After any change do `make parse` and `make typecheck` to ensure no parse or typing errors or introduced.

To play a scenario, do for instance:
```
$ quint -r instances.qnt::simplex_2_parties
> fast_agree_in_view_0
```
