.PHONY: all clean generate-data clean-data regenerate-data

all:
	stack setup && stack build

clean:
	stack clean

generate-data: all
	python generate-data.py

clean-data:
ifneq (,$(wildcard ./generated_data/data.csv))
	rm generated_data/data.csv
endif

regenerate-data: clean-data generate-data
