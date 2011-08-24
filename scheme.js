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
    SBoolean.prototype.toString = function () { return this.value ? "#T" : "#F"; };

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
	    return list.car + (list.cdr !== null ? " " + tostring(list.cdr) : "");
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
    var primitiveFunctionCount = 0;
    function PrimitiveFunction (fn) {
	this.fn = fn;
	this.id = ++primitiveFunctionCount;
    }
    PrimitiveFunction.prototype.toString = function () {
	return "#[procedure " + this.id + "]";
    };

    function VirtualMachine () {
	this.acc = null;
	this.next = null;
	this.env = new Env();

	var vm = this;

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
	this.env.bindings["QUOTE"] = new PrimitiveFunction(function (form, next) {
	    var quote = form.get(1);
	    return { op: 'constant', val: quote, next: next };
	});
    }
    VirtualMachine.prototype.compile = function (form, next) {
	if (form instanceof List) {
	    var fn = form.car;

	    if (fn instanceof Symbol) {
		var fnBinding = this.env.lookup(fn.toString());
		if (fnBinding instanceof PrimitiveFunction) {
		    return fnBinding.fn(form, next);
		}
	    }
	    else {
		return vm.compile(fn, { op: "apply",
					next: next
				      });
	    }
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

	    case "constant":
		this.acc = inst.val;
		this.next = inst.next;
		continue;

	    case "halt":
		return this.acc;

	    case "lookup":
		this.acc = this.env.lookup(inst.name);
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

        code = code.replace(/^[\s\n]*/, "") + " ";//.replace(/\s*$/, "");                                                              
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

    function isApplicable (obj) {
		return obj instanceof PrimitiveFunction;
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

    function schemeRead (str) {
		var tokens = tokenize(str);
		var parsed = parse(tokens);
		return parsed;
    }

    function schemeEval (form) {
		var compiled = vm.compile(form, {op: 'halt'});
		if (DEBUG) {
			console.log("Result of compilation:");
			console.log(compiled);
		}
		var result = vm.exec(compiled);
		if (DEBUG) {
			console.log("New envioronment:");
			console.log(vm.env);
		}
		return result;
    }

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