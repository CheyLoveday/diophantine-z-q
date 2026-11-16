import sys, cypari2
pari = cypari2.Pari(); pari.allocatemem(4*10**9)
pari.default("realprecision", 30)
pari('read("%s")' % sys.argv[1])
