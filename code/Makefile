TARGETS=ToolCmdLine.exe

GENERATE_DATA := python2 generate-data.py
GENERATE_GRAPHS := python2 transform-data.py
CREATE_DEFAULT_ANSWERS := python2 create-default-answers.py

.PHONY: all build clean %.exe

all: build link

build:
	dune build app/ToolCmdLine.exe --profile release # ignores warnings as errors

link: $(TARGETS)

%.exe:
	if [ ! -f $@ ]; then ln -s _build/default/app/$@ . ; fi

install:
	jbuilder install

clean:
	rm -rf _build *.install *.pdf $(TARGETS)

documentation:
	jbuilder build @docs

generate-data: all
	$(GENERATE_DATA) ./ToolCmdLine.exe benchmarks/trace_complete benchmarks/incremental benchmarks/postconditional benchmarks/example_based

generate-outs: all
	$(CREATE_DEFAULT_ANSWERS) ./ToolCmdLine.exe benchmarks/trace_complete benchmarks/incremental benchmarks/postconditional benchmarks/example_based

generate-all: all
	$(GENERATE_DATA) ./ToolCmdLine.exe benchmarks/trace_complete benchmarks/incremental benchmarks/postconditional benchmarks/example_based
	$(GENERATE_GRAPHS) generated_data/generated_data.csv

