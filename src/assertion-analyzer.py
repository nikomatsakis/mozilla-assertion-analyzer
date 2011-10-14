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

# Fixed tokens:
KIND_START = 'START'
KIND_EOF = 'EOF'
KIND_LBRACE = '{'
KIND_RBRACE = '}'
KIND_COLON = ':'
KIND_COLON_COLON = '::'
KIND_LPAREN = '('
KIND_RPAREN = ')'
KIND_COMMA = ','
KIND_SEMI = ';'

# Other tokens:
KIND_ID = 'ID'
KIND_STRING = '""'
KIND_OTHER = '?'

class Token(object):
	def __init__(self, kind, text):
		self.kind = kind
		self.text = text
		
	def is_id(self, text):
		return self.kind == KIND_ID and self.text == text
		
	def __repr__(self):
		return "Token(%r, %r)" % (self.kind, self.text)
		
TOK_START = Token(KIND_START, "")
TOK_EOF = Token(KIND_EOF, "")
TOK_LBRACE = Token(KIND_LBRACE, "{")
TOK_RBRACE = Token(KIND_RBRACE, "}")
TOK_LPAREN = Token(KIND_LPAREN, "(")
TOK_RPAREN = Token(KIND_RPAREN, ")")
TOK_COMMA = Token(KIND_COMMA, ",")
TOK_COLON = Token(KIND_COLON, ":")
TOK_COLON_COLON = Token(KIND_COLON_COLON, "::")
TOK_SEMI = Token(KIND_SEMI, ";")

class ParseError(object):
	def __init__(self, text, offset):
		self.text = text
		self.offset = offset
		
class Tokenizer(object):
	def __init__(self, text):
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
			elif equals('::'):
				self.tok = TOK_COLON_COLON
			elif equals(':'):
				self.tok = TOK_COLON
			elif equals(';'):
				self.tok = TOK_SEMI
			elif equals(','):
				self.tok = TOK_COMMA
			elif equals('"'):
				end = self.find_string_end()
				self.tok = Token(KIND_STRING, self.text[start:end])
			elif equals('/*'):
				self.position = self.find_comment_end()
			elif equals('//'):
				self.position = self.find_next_line()
			elif self.text[self.position].isspace():
				self.position += 1
			else:
				ch = self.text[self.position]
				if ch.isalpha() or ch == '_':
					end = self.find_identifier_end()
					self.tok = Token(KIND_ID, self.text[start:end])
				else:
					self.tok = Token(KIND_OTHER, ch)
		
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
		raise ParseError("Unterminated comment", self.position)
		
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

	def find_string_end(self):
		text = self.text
		position = self.position + 1
		max_position = len(text)
		while position < max_position:
			if text[position] == '"':
				return position + 1
			elif text[position] == '\\':
				position += 2
			else:
				position += 1
		raise ParseError("Unterminated string", self.position)
		
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
		
	def assertion_text(self):
		assert self.tok.kind == KIND_LPAREN
		counter = 1
		text = self.text
		position = start_position = self.position
		max_position = len(text)
		while position < max_position:
			ch = text[position]
			if ch == '(':
				counter += 1
			elif ch == ')' and counter > 1:
				counter -= 1
			elif ch == ')':
				self.position = position + 1
				self.tok = TOK_RPAREN
				return self.text[start_position:position]
			position += 1
		raise ParseError("Unclosed parenthesis", start_position)
		
# __________________________________________________________________
# Assertion Gatherer

class Assertion(object):
	def __init__(self, text, file_name, offset, stmts):
		self.text = text
		self.file_name = file_name
		self.offset = offset
		self.stmts = stmts
		
	def __repr__(self):
		return "Assertion(%r, %r, %r, %r)" % (
			self.text, self.file_name, self.offset, self.stmts)

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
		self.tokenizer = Tokenizer(text)
		self.file_name = file_name
		self.assertions = []
	
	def outer(self):
		while self.tokenizer.tok != TOK_EOF:
			tok = self.tokenizer.next_token()
			if tok.is_id("class"):
				self.class_header()
			elif tok == TOK_LBRACE:
				self.function_body()
		return self.assertions
		
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
			elif tok.is_id("NS_ASSERTION") or tok.is_id("JS_ASSERT"):
				if self.tokenizer.tok == TOK_LPAREN:
					offset = self.tokenizer.position
					text = self.tokenizer.assertion_text()
					assertion = Assertion(text, self.file_name, offset, statements)
					self.assertions.append(assertion)
					
def main(args):
	assertions = []
	for file_name in args:
		text = open(file_name).read()
		a = Gather(file_name, text).outer()
		assertions += a
	for a in assertions:
		print repr(a)
		
main(sys.argv[1:])