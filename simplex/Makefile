parse:
	quint parse simplex.qnt
	quint parse statemachine.qnt
	quint parse instances.qnt

typecheck:
	quint typecheck simplex.qnt
	quint typecheck statemachine.qnt
	quint typecheck instances.qnt

test:
	quint test instances.qnt --main simplex_2_byz --match agreement_failure
	quint test instances.qnt --main simplex_2_parties --match change
	quint test instances.qnt --main simplex_2_parties --match agree
	quint test instances.qnt --main simplex_2_parties_bis --match change
	quint test instances.qnt --main simplex_2_parties_bis --match agree

run:
	quint run instances.qnt --main simplex_2_byz --invariant agreement
