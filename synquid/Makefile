.PHONY: all clean generate-outs generate-data clean-data regenerate-data hyper-clean

all:
	stack setup && stack build

clean:
	stack clean

generate-data: all
	python generate-data.py benchmarks/example-based benchmarks/postconditional

generate-outs: all
	python generate-outs.py benchmarks/example-based benchmarks/postconditional

clean-data:
ifneq (,$(wildcard ./generated-data/data.csv))
	rm generated-data/data.csv
endif

regenerate-data: clean-data generate-data

hyper-clean: clean-data clean
	rm benchmarks/example_based/*.out
	rm benchmarks/postconditional/*.out
