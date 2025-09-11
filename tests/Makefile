.PHONY: gen_example

gen_example: example.ll
	llvm-as example.ll -o example.bc
	llc example.bc -o example.s
	clang example.s -o example

gen_sample: sample.c
	clang -S -emit-llvm sample.c -o sample.ll 	
	clang -S sample.c -o sample.bc

clean:
	rm -rf *.bc *.s example sample.ll


