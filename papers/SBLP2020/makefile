target: all

all : paper.lagda latex/makefile
	agda paper.lagda --latex --only-scope-checking
	$(MAKE) -C latex

clean:
	rm *.agdai
	$(MAKE) -C latex clean
