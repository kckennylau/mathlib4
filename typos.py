# Put me in mathlib4
# Don't forget to add "typos.py", "typos.txt" and "typos-filename.txt" to .git/info/exclude

import os
import re
import sys

freq = dict()
first_seen = dict()

def record(filename, token):
	global freq, first_seen
	if token in freq:
		freq[token] += 1
	else:
		first_seen[token] = filename
		freq[token] = 1

def process(filename, file):
	tokens = re.findall("[A-Z]?[a-z]+", file)
	for token in tokens:
		token = token.lower()
		record(filename, token)

count = 0
for root, dirs, files in os.walk('Mathlib'):
	for file in files:
		filename = os.path.join(root, file)
		with open(filename, "r", encoding="UTF-8") as auto:
			count += 1
			if count % 100 == 0:
				sys.stdout.write("\r%d files processed."%count)
				sys.stdout.flush()
			process(filename, auto.read())

report ="%d files processed.\n"%count
report+="Number of distinct tokens: %d\n"%len(freq)
report+="Total number of tokens: %d\n\n"%(sum(freq[i] for i in freq))

print("\r"+report)

typos_name = open("typos-filename.txt", "w")
typos = open("typos.txt", "w")

typos_name.write(report)
typos.write(report)

keys = sorted(freq.keys(), key=lambda n:(freq[n],n))
for key in keys:
	typos_name.write("%s, %s, %s\n"%(key, freq[key], first_seen[key]))
	typos.write("(%s, %s),"%(key, freq[key]))

typos_name.close()
typos.close()
