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
	quint test instances.qnt --main simplex_2_parties --match path
	quint test instances.qnt --main simplex_2_parties_bis --match change
	quint test instances.qnt --main simplex_2_parties_bis --match path

run:
	quint run instances.qnt --main simplex_2_parties --invariant agreement
	quint run instances.qnt --main simplex_2_parties_bis --invariant agreement
	quint run instances.qnt --main simplex_2_byz --invariant agreement
