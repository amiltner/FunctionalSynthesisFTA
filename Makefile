.PHONY: all clean generate-data clean-data regenerate-data

all:
	make -C code
	make -C synquid

clean:
	make -C code clean

clean-data:
	make -C code clean-data

generate-data:
	make -C code generate-data
	make -C synquid generate-data

regenerate-data:
	make -C code regenerate-data
	make -C synquid regenerate-data

graphs:
	python3 generate-graphs.py generated-data/examples.csv generated-data/equiv.csv generated-data/postconditional.csv
