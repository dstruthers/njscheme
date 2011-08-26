var Scheme = function () {
    const DEBUG = true;

    // Built-in Scheme types

    function Symbol (name) {
	this.name = new String(name);
    }
    Symbol.prototype.toString = function () { return this.name.toUpperCase(); };

    function SNumber (n) {
	this.value = new Number(n);
    }
    SNumber.prototype.toString = function () { return this.value.toString(); };

    function SString (s) {
	this.value = new String(s);
    }
    SString.prototype.toString = function () { return "\"" + this.value + "\""; };

    function SBoolean (b) {
	if (typeof(b) === "string") {
	    this.value = (b.toLowerCase() === "#f") ? false : true;
	}
	else {
	    this.value = new Boolean(b);
	}
    }
    SBoolean.prototype.toString = function () { return this.value.valueOf() ? "#T" : "#F"; };

    function List (items) {
	var itemsCopy = arrayCopy(items);
	if (!(itemsCopy instanceof Array)) {
	    this.car = itemsCopy;
	    this.cdr = null;
	}
	else {
	    this.car = itemsCopy.shift();
	    this.cdr = itemsCopy.length > 0 ? new List(itemsCopy) : null;
	}
    }
    List.prototype.toString = function () {
	function tostring (list) {
	    return (list.car !== null && list.car !== undefined ? list.car + (list.cdr !== null ? " " + tostring(list.cdr) : "") : "");
	}
	return "(" + tostring(this) + ")";
    };
    List.prototype.get = function (offset) {
	if (offset === 0) {
	    return this.car;
	}
	else {
	    return this.cdr.get(offset - 1);
	}
    }
    List.prototype.length = function () {
	if (this.cdr instanceof List) {
	    return 1 + this.cdr.length();
	}
	else {
	    return this.car == null ? 0 : 1;
	}
    };

    // Environment

    function Env (parent) {
	this.bindings = {};
    }
    Env.prototype.lookup = function (name) {
	if (this.bindings[name] !== undefined) {
	    return this.bindings[name];
	}
	else if (this.parent) {
	    return this.parent.lookup(name);
	}
	else {
	    throw "Unbound variable: " + name;
	}
    };

    // Closures

    function Closure (env, vars, body) {
	this.env = env;
	this.vars = vars;
	this.body = body;
    }
    Closure.prototype.toString = function () { return "#[Lexical closure]"; };

    // Virtual Machine / compilation
    function PrimitiveFunction (fn) {
	this.fn = fn;
    }
    PrimitiveFunction.prototype.toString = function () {
	return "#[Primitive procedure]";
    };

    function PrimitiveApplicable (op) {
	this.fn = function (form, next) {
	    var argCount = form.length() - 1;

	    function comp (compiled, i) {
		if (i === argCount) {
		    if (next.op === "return") {
			return compiled;
		    }
		    else {
			return { op: "frame",
				 ret: next,
				 next: compiled
			       };
		    }
		}
		else {
		    return comp(vm.compile(form.get(i + 1), { op: "argument", next: compiled }), i + 1);
		}
	    }
	    return comp({ op: op, next: { op: "return", next: next } }, 0);
	}
    }
    PrimitiveApplicable.prototype.toString = function () { return "#[Primitive procedure]"; };

    function VirtualMachine () {
	this.acc = null;
	this.next = null;
	this.env = new Env();
	this.args = [];
	this.stack = null;

	var vm = this;

	this.env.bindings["+"] = new PrimitiveApplicable("add");
	this.env.bindings["-"] = new PrimitiveApplicable("subtract");
	this.env.bindings["*"] = new PrimitiveApplicable("multiply");
	this.env.bindings["="] = new PrimitiveApplicable("equal-numer");
	this.env.bindings["CALL-WITH-CURRENT-CONTINUATION"] = new PrimitiveFunction(function (form, next) {
	    var fn = form.get(1);
	    var compiled = { op: "conti",
			     next: { op: "argument",
				     next: vm.compile(fn, { op: "apply" })
				   }
			   };
	    if (next.op === "return") {
		return compiled;
	    }
	    else {
		return { op: "frame",
			 ret: next,
			 next: compiled
		       };
	    }
	});
	this.env.bindings["CAR"] = new PrimitiveFunction(function (form, next) {
	    var list = form.get(1);
	    return vm.compile(list, { op: "car", next: next });
	});
	this.env.bindings["CDR"] = new PrimitiveFunction(function (form, next) {
	    var list = form.get(1);
	    return vm.compile(list, { op: "cdr", next: next });
	});
	this.env.bindings["DEFINE"] = new PrimitiveFunction(function (form, next) {
	    var name = form.get(1);
	    var value = form.get(2);

	    return vm.compile(value,
			      { op: 'assign',
				name: name,
				next: next
			      });
	});
	this.env.bindings["IF"] = new PrimitiveFunction(function (form, next) {
	    var test = form.get(1);
	    var consequent = form.get(2);
	    var alternative = form.get(3);

	    return vm.compile(test,
			      { op: "test",
				consequent: vm.compile(consequent, next),
				alternative: vm.compile(alternative, next)
			      }
			     );
	});
	this.env.bindings["LAMBDA"] = new PrimitiveFunction(function (form, next) {
	    var params = form.get(1);
	    var body = form.get(2);

	    return { op: "closure",
		     vars: params,
		     body: vm.compile(body, { op: "return" }),
		     next: next
		   };
	});
	this.env.bindings["NOT"] = new PrimitiveFunction(function (form, next) {
	    var arg = form.get(1);
	    return vm.compile(arg, { op: "not",
				     next: next
				   }
			     );
	});
	this.env.bindings["NULL?"] = new PrimitiveFunction(function (form, next) {
	    var arg = form.get(1);
	    return vm.compile(arg, { op: "isnull",
				     next: next
				   }
			     );
	});
	this.env.bindings["QUOTE"] = new PrimitiveFunction(function (form, next) {
	    var quote = form.get(1);
	    return { op: 'constant', val: quote, next: next };
	});
    }
    VirtualMachine.prototype.compile = function (form, next) {
	if (form instanceof List) {
	    var fn = form.car;

	    if (fn instanceof Symbol) {
		try {
		    var fnBinding = this.env.lookup(fn.toString());
		    if (isApplicable(fnBinding)) {
			return fnBinding.fn(form, next);
		    }
		}
		catch (e) {
		}
	    }
	    
	    // otherwise assume application
	    var argCount = form.length() - 1;
	    var vm = this;

	    function comp (compiled, i) {
		if (i === argCount) {
		    if (next.op === "return") {
			return compiled;
		    }
		    else {
			return { op: "frame",
				 ret: next,
				 next: compiled
			       };
		    }
		}
		else {
		    return comp(vm.compile(form.get(i + 1), { op: "argument", next: compiled }), i + 1);
		}
	    }
	    return comp(this.compile(fn, { op: "apply", next: next }), 0);

	}
	else if (isConstant(form)) {
	    return { op: "constant",
		     val: form,
		     next: next
		   };
	}
	else if (form instanceof Symbol) {
	    return { op: "lookup",
		     name: form,
		     next: next
		   };
	}
	else {
	    throw "Error during compilation";
	}
    };

    VirtualMachine.prototype.exec = function (code) {
	this.next = code;
	while (true) {
	    var inst= this.next;

	    switch (inst.op) {
	    case "add":
		var addAcc = 0;
		while (true) {
		    var n = this.args.pop();
		    if (n === undefined) {
			break;
		    }
		    if (!(n instanceof SNumber)) {
			throw "Cannot add non-numeric term " + n.toString();
		    }
		    addAcc += n.value.valueOf();
		}
		this.acc = new SNumber(addAcc);
		this.next = inst.next;
		continue;

	    case "apply":
		var env = new Env(this.acc.env);
		for (var i = 0; i < this.acc.vars.length(); i++) {
		    var varName = this.acc.vars.get(i).toString();
		    var varVal = this.args.pop();
		    env.bindings[varName] = varVal;
		}
		this.env = env;
		this.next = this.acc.body;
		continue;

	    case "argument":
		this.args.push(this.acc);
		this.next = inst.next;
		continue;

	    case "assign":
		this.env.bindings[inst.name] = this.acc;
		this.next = inst.next;
		continue;

	    case "car":
		this.acc = this.acc.car;
		this.next = inst.next;
		continue;

	    case "cdr":
		this.acc = this.acc.cdr;
		this.next = inst.next;
		continue;

	    case "closure":
		this.acc = new Closure(this.env, inst.vars, inst.body);
		this.next = inst.next;
		continue;

	    case "cons":
		var head = inst.elem;
		var tail = inst.list;
		var list = new List();
		list.car = head;
		list.cdr = tail;
		this.acc = list;
		this.next = inst.next;
		continue;

	    case "constant":
		this.acc = inst.val;
		this.next = inst.next;
		continue;

	    case "conti":
		this.acc = new Closure(new Env(),
				       new List([new Symbol("v")]),
				       { op: "nuate",
					 name: "V",
					 stack: this.stack
				       });
		this.next = inst.next;
		continue;

	    case "equal-numer":
		var equalAcc = null;
		var equal = true;
		while (true) {
		    var n = this.args.pop();
		    if (n === undefined) {
			break;
		    }
		    if (!(n instanceof SNumber)) {
			throw "Cannot compare non-numeric term " + n.toString();
		    }
		    if (equalAcc === null) {
			equalAcc = n.value.valueOf();
		    }
		    else {
			if (n.value.valueOf() !== equalAcc) {
			    equal = false;
			    break;
			}
		    }
		}
		this.acc = new SBoolean(equal);
		this.next = inst.next;
		continue;

	    case "finish":
		return this.acc;

	    case "frame":
		this.stack = { next: inst.ret,
			       env: this.env,
			       args: this.args,
			       stack: this.stack
			     };
		this.args = [];
		this.next = inst.next;
		continue;

	    case "isnull":
		this.acc = new SBoolean(isNull(this.acc));
		this.next = inst.next;
		continue;

	    case "lookup":
		this.acc = this.env.lookup(inst.name);
		this.next = inst.next;
		continue;

	    case "multiply":
		var multAcc = 1;
		while (true) {
		    var n = this.args.pop();
		    if (n === undefined) {
			break;
		    }
		    if (!(n instanceof SNumber)) {
			throw "Cannot multiply non-numeric term " + n.toString();
		    }
		    multAcc *= n.value.valueOf();
		}
		this.acc = new SNumber(multAcc);
		this.next = inst.next;
		continue;

	    case "not":
		if (!(this.acc instanceof SBoolean)) {
		    var result = new SBoolean(false);
		}
		else {
		    var result = new SBoolean(!this.acc.value.valueOf());
		}
		this.acc = result;
		this.next = inst.next;
		continue;

	    case "nuate":
		this.acc = this.env.lookup(inst.name);
		this.next = { op: "return" };
		this.stack = inst.stack;
		continue;

	    case "return":
		this.next = this.stack.next;
		this.env = this.stack.env;
		this.args = this.stack.args;
		this.stack = this.stack.stack;
		continue;

	    case "subtract":
		var subAcc = null;
		while (true) {
		    var n = this.args.pop();
		    if (n === undefined) {
			break;
		    }
		    if (!(n instanceof SNumber)) {
			throw "Cannot subtract non-numeric term " + n.toString();
		    }
		    if (subAcc === null) {
			subAcc = n.value.valueOf();
		    }
		    else {
			subAcc -= n.value.valueOf();
		    }
		}
		this.acc = new SNumber(subAcc);
		this.next = inst.next;
		continue;

	    case "test":
		this.next = isTrue(this.acc) ? inst.consequent : inst.alternative;
		continue;

	    default:
		throw "Unknown instruction: " + inst.op;
	    }
	}
    };

    // Parsing

    function CommentToken (token) { this.token = token; }
    function SExpressionBeginToken (token) { this.token = token; }
    function SExpressionEndToken (token) { this.token = token; }
    function VectorBeginToken (token) { this.token = token; }
    function QuoteToken (token) { this.token = token; }
    function QuasiQuoteToken (token) { this.token = token; }
    function UnquoteSplicingToken (token) { this.token = token; }
    function UnquoteToken (token) { this.token = token; }

    function tokenize (code) {
        var matches = null;
        var token_types = [
            [CommentToken,          /^(;[^\n]*)/              ],
            [SExpressionBeginToken, /^(\()/                   ],
            [SExpressionEndToken,   /^(\))/                   ],
            [VectorBeginToken,      /^(#\()/                  ],
            [QuoteToken,            /^(\')/                   ],
            [QuasiQuoteToken,       /^(`)/                    ],
            [UnquoteSplicingToken,  /^(,@)/                   ],
            [UnquoteToken,          /^(,)/                    ],
            [SString,               /^\"((?:[^\"\\]|\\.)*)\"/ ],
            [SBoolean,              /^(#[tf]{1})([\s\n\(\)])/i          ],
            [SNumber,               /^([\+\-]?(?:[0-9]+(?:\.[0-9]*)?|\.[0-9]+))([\s\n\(\)])/],
            [Symbol,                /^([^\(\)\[\]\"\s]+)/     ]
        ];

        code = code.replace(/^[\s\n]*/, "") + " ";
        for (var i = 0; i < token_types.length; i++) {
            if (matches = code.match(token_types[i][1])) {
                var replacement = matches.length > 2
                    ? matches[2]
                    : "";
                return [new token_types[i][0](matches[1])]
                    .concat(tokenize(code.replace(token_types[i][1],
                                                  replacement)));
            }
        }
        return [];
    }

    function parse (tokens) {
        var limit = arguments.length > 1
            ? arguments[1]
            : -1;

        if (tokens.length === 0 || limit === 0) {
            return [];
        }

        var token = tokens.shift();

        // Core parsing for symbols, literals, and s-expressions
        if (token instanceof Symbol || token instanceof SBoolean
            || token instanceof SNumber || token instanceof SString) {
            return [token].concat(parse(tokens, limit - 1));
        }
        else if (token instanceof SExpressionBeginToken) {
            var contents = parse(tokens);
            return [new List(contents)].concat(parse(tokens, limit - 1));
        }
        else if (token instanceof SExpressionEndToken) {
            return [];
        }

	// Syntactic sugar
	else if (token instanceof QuoteToken) {
            var contents = [new Symbol("quote")];
            contents = contents.concat(parse(tokens, 1));
            return [new List(contents)].concat(parse(tokens, limit - 1));
	}

        // Ignore comments
        else if (token instanceof CommentToken) {
            return parse(tokens, limit);
        }

        // something went wrong
        else {
            throw "Cannot parse: " + token;
        }
    }


    // utility functions

    function isConstant (atom) {
	return atom instanceof SString
	    || atom instanceof SNumber
	    || atom instanceof SBoolean;
    }

    function isTrue (atom) {
	return !(atom instanceof SBoolean) || atom.value !== false;
    }

    function isNull (list) {
	return list instanceof List && (list.car === null || list.car === undefined);
    }

    function isApplicable (obj) {
	return obj.fn && typeof(obj.fn) === "function";
    }

    function arrayCopy (a) {
	var b = [];
	for (var i = 0; i < a.length; i++) {
	    if (a[i] instanceof Array) {
		b[i] = arrayCopy(a[i]);
	    }
	    else {
		b[i] = a[i];
	    }
	}
	return b;
    }

    function printObj (o) {
	var r = "{\n";
	for (var prop in o) {
	    r += prop + ": " + o[prop] + "\n";
	}
	r += "}";
	return r;
    }

    // REPL
    var vm = new VirtualMachine();

    function run (code) {
	var tokens = tokenize(code);
	var parsed = parse(tokens);
	for (var i = 0; i < parsed.length; i++) {
	    var compiled = vm.compile(parsed[i], { op: "finish" });
	    vm.exec(compiled);
	}
    }

    function schemeRead (str) {
	var tokens = tokenize(str);
	var parsed = parse(tokens);
	return parsed;
    }

    function schemeEval (form) {
	var compiled = vm.compile(form, {op: 'finish'});
	if (DEBUG) {
	    console.log("Result of compilation:");
	    console.log(compiled);
	}
	var result = vm.exec(compiled);
	if (DEBUG) {
	    console.log("New environment:");
	    console.log(vm.env);
	}
	return result;
    }

    // some shortcuts
    run("(define call/cc call-with-current-continuation)");

    return {
	Env: Env,
	VirtualMachine: VirtualMachine,
	Symbol: Symbol,
	String: SString,
	Number: SNumber,
	Boolean: SBoolean,
	List: List,
	tokenize: tokenize,
	parse: parse,
	read: schemeRead,
	eval: schemeEval
    };
}();