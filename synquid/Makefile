.PHONY: all clean generate-outs generate-data clean-data regenerate-data hyper-clean clean-outs regenerate-outs

all:
	stack setup && stack build

clean:
	stack clean

generate-data: all
	python3 generate-data.py benchmarks/example-based benchmarks/postconditional

generate-outs: all
	python3 generate-outs.py benchmarks/example-based benchmarks/postconditional

clean-data:
ifneq (,$(wildcard ./generated-data/data.csv))
	rm generated-data/data.csv
endif

regenerate-data: clean-data generate-data

regenerate-outs: clean-outs generate-outs

clean-outs:
	rm benchmarks/postconditional/*.out
	rm benchmarks/example_based/*.out

hyper-clean: clean-data clean-outs clean
