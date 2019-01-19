import std.stdio;


import pegged.grammar;

/**
IFF: <->
IMP: ->
AND: &
OR:  |
NOT: ~
*/
mixin(grammar(`
Expr:
    IFF      < IMP ("<->" IFF)*
	IMP	     < OR ("->" IMP)*
	OR       < AND ("|" OR)*
	AND      < NOT ("&" AND)*
	NOT      < "~"? Primary 
	Primary  < Parens / Constant / Variable
    Parens   < "(" IFF ")"
	Constant < "true" / "false"
    Variable <- identifier
`));
/*
mixin(grammar(`
Expr:
	S   <  IFF / IMP / AND / OR / NOT / Parens / Variable / Constant
    IFF < S :"<->" S 
    IMP < S :"|" S 
    AND < S :"&" S 
    OR  < S :"|" S 
	NOT < :"~" S 
	Primary  < Parens / Constant / Variable
    Parens   < :"(" S :")"
	Constant < "true" / "false"
    Variable <- identifier
`));
*/

//import std.variant;
//import std.typecons : Tuple , tuple;
import std.format;


//struct BOp {Expr left, right; int type;}
//alias BOp = Tuple!(string, Node*, Node*);
//alias UOp = Tuple!(string, Node*);
//struct UOp {Expr sub; int type;}
/*
	alias Node = Algebraic!(string, 
	Tuple!(string, This*, This*),
	Tuple!(string, This*, This*));
*/

enum NType  {
	VAR, IFF, IMP, AND, OR, NOT, CONST
}

class Node {
	NType type; 
}

class Var :  Node {
	string name; 
	this(string v) { name = v;}
	override string toString()  {
		return name;
	}
}

class Const :  Node { 
	bool value; 
	this(bool v) { value = v;}

	static Const TRUE, FALSE;

	static this() {
		TRUE = new Const(true);
		FALSE = new Const(false);
	}

	override string toString()   {
		return value ? "true" : "false";
	}
}

class BOp : Node { 
	Node left, right;
	this(NType type, Node left, Node right) {
		this.type = type; 
		this.left = left;
		this.right = right;
	}

	override string toString()  {
		return format!"(%s %s %s)"(left.toString(), type, right.toString());
	}
}

class UOp : Node { 	
	Node sub;
	this(NType type, Node sub) {
		this.type = type;
		this.sub = sub;
	}

	override string toString()  {
		return format!"(%s %s)"(type, sub.toString());
	}
}

unittest{ 
	Node n = Const.TRUE;
}

Node parseToCode(ParseTree p) {
	switch(p.name) {
		case "Expr.Variable": 
			return new Var(p.matches[0]);
		case "Expr.Parens":
		case "Expr":
		case "Expr.Primary":
			return parseToCode(p.children[0]);
		case "Expr.Constant":
			return (p.matches[0] == "true") ?  Const.TRUE : Const.FALSE;
		case "Expr.IFF":
		case "Expr.IMP":		
		case "Expr.AND":
		case "Expr.OR":
			if(p.children.length == 2) {
				auto op = NType.IFF; 
				final switch(p.name) {
					case "Expr.IFF": op = NType.IFF; break;
					case "Expr.IMP": op = NType.IMP; break;
					case "Expr.AND": op = NType.AND; break;
					case "Expr.OR":  op = NType.OR; break;
				}
				return new BOp(op, parseToCode(p.children[0]), parseToCode(p.children[1]));
			}
			return parseToCode(p.children[0]);
		case "Expr.NOT":
			return p.matches.length  == 1
				? parseToCode(p.children[0])
				: new UOp(NType.NOT, parseToCode(p.children[0]));
		default: 
			writeln(p.name);
			assert(0);
	}
}

/**
 * rewrite the AST: removal 
 */
Node reduce(Node n) { 
	final switch(n.type) {
		case NType.IFF:
			BOp iff = cast(BOp) n;
			auto a = iff.left;
			auto b = iff.right;
			BOp left = new BOp(NType.OR, new UOp(NType.NOT, a), b);
			BOp right = new BOp(NType.OR, new UOp(NType.NOT, b), a);
			BOp and = new BOp(NType.AND, left, right);
			return and;
		case NType.IMP:
			BOp imp = cast(BOp) n;
			return new BOp(NType.OR, new UOp(NType.NOT, imp.left), imp.right);
		case NType.NOT:
		case NType.AND:
		case NType.OR:
		case NType.VAR:
		case NType.CONST:
			return n;
	}
}

void writeClause(int[] clause...){
	writeClause(clause);
}


void writeClause(int[] clause){
	 foreach(l;  clause) {
		 write(l);
		 write(" ");
	 }
	 writeln("0");
}


int currentVar = 0;
int[string] variables;
int trueLit = 0, falseLit = 0;

int tseityn(Node n) { 
	final switch(n.type) {
		case NType.IFF:
			assert(0);
		case NType.IMP:
			assert(0);
		case NType.NOT:
			return -tseityn((cast(UOp)n).sub);
		case NType.AND:
			/* 1. r <-> a & b
			   2a. r -> a&b = ~r | a&b 
			   3aa. ~r | a
			   3ab. ~r | b
			   2b. a&b -> r =  ~a|~b|r
			*/
			BOp and = cast(BOp) n;		
			auto r = ++currentVar;
			auto a = tseityn(and.left);
			auto b = tseityn(and.right);
			writeClause(-r, a);
			writeClause(-r, b);
			writeClause(-a,-b,r);
			return r;
		case NType.OR:
			/* 1. r <-> a | b
			   2a. r -> a|b = ~r|a|b 
			   2b. a|b -> r =  (~a&~b)|r
			   3ba. ~a | r
			   3bb. ~b | r
			*/
			BOp and = cast(BOp) n;		
			auto r = ++currentVar;
			auto a = tseityn(and.left);
			auto b = tseityn(and.right);
			writeClause(-r, a, b);
			writeClause(-a,r);
			writeClause(-b,r);
			return r;
		case NType.VAR:
			auto var = cast(Var) n;
			//auto lit = variables.require(var.name, variables + 1);		
			if((var.name in variables) == null){
				variables[var.name] = ++currentVar;
			}
			auto lit = variables[var.name];
			writeln("c Variable %s = %d.");
			return lit;
		case NType.CONST:
			auto c = cast(Const) n;
			if(c.value) {
				if(trueLit == 0) addTrueLiteral();
				return trueLit;
			} else {
				if(falseLit == 0) addFalseLiteral();
				return falseLit;
			}
	}
}

int addTrueLiteral() {
	// true <-> a | -a
	BOp op = new BOp(NType.OR, new Var("__unused__"), 
		new UOp(NType.NOT, new Var("__unused__")));
	return trueLit = tseityn(op);
}

int addFalseLiteral() {
	// true <-> a & -a
	BOp op = new BOp(NType.AND, new Var("__unused__"), 
		new UOp(NType.NOT, new Var("__unused__")));
	return falseLit = tseityn(op);
}

unittest {
	void test(string expr) {
		auto parseTree2 = Expr(expr);
		//writeln(parseTree2);	
		auto n = parseToCode(parseTree2);
		writeln(n.toString());
	}

	test("x");
	test("~abc");
	test("a & b");
	test("a & b");
	test("a | b & c");	
	test("a & b | c");	

	auto n = reduce(parseToCode(Expr("a <-> b")));
	writeln(n.toString());

	auto x = tseityn(
		new UOp(NType.NOT, new Var("x")));
	writeClause(x);
}

void main()
{
	writeln("Edit source/app.d to start your project.");
}
