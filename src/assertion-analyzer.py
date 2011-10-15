import re
import sys

# Basic plan: to scan through a C++ or C file, detecting when we enter
# into a function and detecting when assertions occur.  In the latter case,
# we will use regular expressions to classify those assertions.  We will
# also categorize the assertion based on where in the function it occurred:
# very beginning or middle.  
#
# In an ideal world, we would also classify the assertion based on whether
# it references parameters, local variables, etc, but I think that for now
# we will use the heuristic that assertions in the beginning are most
# likely referring to parameters.

# __________________________________________________________________
# Very simple C tokenizer

class Token(object):
	def __init__(self, kind, text):
		self.kind = kind
		self.text = text
		
	def is_id(self, text):
		return self.kind == 'ID' and self.text == text
		
	def __repr__(self):
		return "Token(%r, %r)" % (self.kind, self.text)
		
TOK_START = Token('START', "")
TOK_EOF = Token('EOF', "")
TOK_LBRACE = Token('{', "{")
TOK_RBRACE = Token('}', "}")
TOK_LPAREN = Token('(', "(")
TOK_RPAREN = Token(')', ")")
TOK_LBRACKET = Token('[', '[')
TOK_RBRACKET = Token(']', ']')
TOK_LT = Token('<', "<")
TOK_GT = Token('>', ">")
TOK_COMMA = Token(',', ",")
TOK_COLON = Token(':', ":")
TOK_COLON_COLON = Token('::', "::")
TOK_SEMI = Token(';', ";")
TOK_EQ = Token('=', "=")

class ParseError(Exception):
	def __init__(self, text, file_name, offset):
		self.file_name = file_name
		self.text = text
		self.offset = offset
		
class Tokenizer(object):
	def __init__(self, file_name, text):
		self.file_name = file_name
		self.text = text
		self.position = 0
		self.tok = TOK_START
		
	def next_token(self):
		def equals(txt):
			return self.text.startswith(txt, self.position)
		
		prev_tok = self.tok
		#print "Consumed " + repr(prev_tok)
		self.tok = None
		while self.tok is None:
			start = self.position
			if start == len(self.text):
				self.tok = TOK_EOF
			elif equals('('):
				self.tok = TOK_LPAREN
			elif equals(')'):
				self.tok = TOK_RPAREN
			elif equals('{'):
				self.tok = TOK_LBRACE
			elif equals('}'):
				self.tok = TOK_RBRACE
			elif equals('['):
				self.tok = TOK_LBRACKET
			elif equals(']'):
				self.tok = TOK_RBRACKET
			elif equals('::'):
				self.tok = TOK_COLON_COLON
			elif equals(':'):
				self.tok = TOK_COLON
			elif equals(';'):
				self.tok = TOK_SEMI
			elif equals(','):
				self.tok = TOK_COMMA
			elif equals('"') or equals("'"):
				end = self.find_string_end(self.text[self.position])
				self.tok = Token('STRING', self.text[start:end])
			elif equals('/*'):
				self.position = self.find_comment_end()
			elif equals('//'):
				self.position = self.find_next_line()
			elif equals('='):
				self.tok = TOK_EQ
			elif self.text[self.position].isspace():
				self.position += 1
			else:
				ch = self.text[self.position]
				if ch.isalpha() or ch == '_':
					end = self.find_identifier_end()
					self.tok = Token('ID', self.text[start:end])
				else:
					self.tok = Token('OTHER', ch)
		
		self.position += len(self.tok.text)
		return prev_tok
		
	def find_comment_end(self):
		text = self.text
		position = self.position + 1
		max_position = len(text)
		while position < max_position:
			if text.startswith("*/", position):
				return position + 2
			else:
				position += 1
		raise ParseError("Unterminated comment", self.file_name, self.position)
		
	def find_next_line(self):
		text = self.text
		position = self.position + 1
		max_position = len(text)
		while position < max_position:
			if text.startswith("\n", position):
				return position + 1
			else:
				position += 1
		return position

	def find_string_end(self, kind):
		text = self.text
		position = self.position + 1
		max_position = len(text)
		while position < max_position:
			if text[position] == kind:
				return position + 1
			elif text[position] == '\\':
				position += 2
			else:
				position += 1
		raise ParseError("Unterminated string", self.file_name, self.position)
		
	def find_identifier_end(self):
		text = self.text
		position = self.position + 1
		max_position = len(text)
		while position < max_position:
			ch = text[position]
			if ch.isalpha() or ch == '_' or ch.isdigit():
				position += 1
			else:
				break
		return position
		
	def assertion_contents(self):
		assert self.tok == TOK_LPAREN
		start_position = self.position
		counter = 1
		contents = []
		while self.next_token() != TOK_EOF:
			if self.tok == TOK_RPAREN and counter > 1:
				counter -= 1
			elif self.tok == TOK_RPAREN:
				end_position = self.position - len(self.tok.text)
				contents += [self.text[start_position:end_position].strip()]
				return contents
			elif self.tok == TOK_LPAREN:
				counter += 1
			elif self.tok == TOK_COMMA and counter == 1:
				end_position = self.position - len(self.tok.text)
				contents += [self.text[start_position:end_position].strip()]
				start_position = self.position + 1
		raise ParseError("Unclosed parenthesis", self.file_name, start_position)
		
# __________________________________________________________________
# Assertion Gatherer

class Assertion(object):
	def __init__(self, contents, file_name, offset, prelude, stmts):
		self.expr = contents[0]
		self.file_name = file_name
		self.offset = offset
		self.prelude = prelude
		self.stmts = stmts
		
	def is_null_check(self):
		return re.match("^\w+$", self.expr) is not None
		
	def __repr__(self):
		return "Assertion(%r, %r, %r, %r, %r)" % (
			self.expr, self.file_name, self.offset, self.prelude, self.stmts)

# Start in state OUTER.
#
# If we see the CLASS keyword followed by LBRACE, enter state CLASS until
# a matching RBRACE.
#
# In CLASS or OUTER state, if we see a LPAREN, remember the ID as the
# function name.  If we see a LBRACE, enter FUNCTION state.
#
# In FUNCTION state, count the semicolons and scan for matching RBRACE.
# If we see NS_ASSERT or JS_ASSERT followed by LPAREN, capture until matching
# RPAREN.

class Gather(object):
	def __init__(self, file_name, text):
		self.tokenizer = Tokenizer(file_name, text)
		self.file_name = file_name
		self.assertions = []
	
	def outer(self):
		while self.tokenizer.tok != TOK_EOF:
			tok = self.tokenizer.next_token()
			if tok.is_id("class"):
				self.class_header()
			#elif tok.is_id("namespace"):
			#	self.namespace_header()
			elif tok == TOK_LBRACE:
				self.function_body()
		return self.assertions
		
	def namespace_header(self):
		while self.tokenizer.tok != TOK_EOF:
			tok = self.tokenizer.next_token()
			if tok == TOK_SEMI or tok == TOK_LBRACE:
				return
		
	def class_header(self):
		while self.tokenizer.tok != TOK_EOF:
			tok = self.tokenizer.next_token()
			if tok == TOK_SEMI:
				return
			if tok == TOK_LBRACE:
				return self.class_body()
				
	def class_body(self):
		while self.tokenizer.tok != TOK_EOF:
			tok = self.tokenizer.next_token()
			if tok == TOK_RBRACE:
				return
			if tok == TOK_LBRACE:
				self.function_body()
	
	def function_body(self):
		nesting = 1
		statements = 0
		prelude = True
		while self.tokenizer.tok != TOK_EOF:
			tok = self.tokenizer.next_token()
			if tok == TOK_RBRACE:
				statements += 1
				nesting -= 1
				if not nesting:
					return
			elif tok == TOK_LBRACE:
				nesting += 1
			elif tok == TOK_SEMI:
				statements += 1
			elif tok in [TOK_EQ, TOK_LPAREN] or tok.kind == 'OTHER':
				prelude = False
			elif tok.is_id("NS_ASSERTION") or tok.is_id("JS_ASSERT"):
				if self.tokenizer.tok == TOK_LPAREN:
					offset = self.tokenizer.position
					contents = self.tokenizer.assertion_contents()
					assertion = Assertion(
						contents, self.file_name, 
						offset, prelude, statements)
					self.assertions.append(assertion)
					
# __________________________________________________________________
# Summarize

def summarize(assertions):
	in_prelude = [a for a in assertions if a.prelude]
	null_in_prelude = [a for a in in_prelude if a.is_null_check()]
	in_body = [a for a in assertions if not a.prelude]
	null_in_body = [a for a in in_body if a.is_null_check()]
	
	la = float(len(assertions))
	lp = float(len(in_prelude))
	lnp = float(len(null_in_prelude))
	lb = float(len(in_body))
	lnb = float(len(null_in_body))
	
	print "Total assertions: %.0f" % la
	print "In prelude: %.0f (%3.0f%%)" % (
		lp, 100.0 * lp / la)
	print "      null: %.0f (%3.0f%% / %3.0f%%)" % (
		lnp, 100.0 * lnp / la, 100.0 * lnp / lp)
	print "In body:    %.0f (%3.0f%%)" % (
		lb, 100.0 * lb / la)
	print "      null: %.0f (%3.0f%% / %3.0f%%)" % (
		lnb, 100.0 * lnb / la, 100.0 * lnb / lb)
					
def main(args):
	assertions = []
	for file_name in args:
		text = open(file_name).read()
		try:
			a = Gather(file_name, text).outer()
			assertions += a
		except ParseError, e:
			line_num = text[:e.offset].count("\n")+1
			print "%s:%d: %s" % (file_name, line_num, e.text)
	for a in assertions:
		print repr(a)
	summarize(assertions)
		
main(sys.argv[1:])
