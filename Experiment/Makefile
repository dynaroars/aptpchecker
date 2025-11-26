NEURALSAT_DIR = /home/roars/neuralsat_proof/src
ABCROWN_DIR = /home/roars/APTPchecker/Experiment/ref/abcrown/complete_verifier/

RESULT_DIR = result/
RESULT_BUG_DIR = result_bug/


all: neuralsat

neuralsat: neuralsat_input neuralsat_hidden

neuralsat_input:
	python3 runner.py --verifier neuralsat --split_type input --verifier_dir $(NEURALSAT_DIR) --result_dir $(RESULT_DIR)

neuralsat_hidden:
	python3 runner.py --verifier neuralsat --split_type hidden --verifier_dir $(NEURALSAT_DIR) --result_dir $(RESULT_DIR)

neuralsat_bug:
	NEURALSAT_SYNTHETIC_BUG_DROP_PROBABILITY=0.2 python3 runner.py --verifier neuralsat --split_type hidden --verifier_dir $(NEURALSAT_DIR) --result_dir $(RESULT_BUG_DIR)

abcrown: abcrown_input abcrown_hidden

abcrown_input:
	python3 runner.py --verifier abcrown --split_type input --verifier_dir $(ABCROWN_DIR) --result_dir $(RESULT_DIR)

abcrown_hidden:
	python3 runner.py --verifier abcrown --split_type hidden --verifier_dir $(ABCROWN_DIR) --result_dir $(RESULT_DIR)