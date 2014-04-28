import haxe.macro.Type;
import haxe.macro.Expr;
using haxe.macro.Tools;
import haxe.macro.Context;
import haxe.macro.Compiler;
import haxe.macro.JSGenApi;
using Lambda;
using StringTools;

class ExampleGen{

  var api : JSGenApi;
  var buf : StringBuf;
  var inits : List<TypedExpr>;
  var metas : Array<String> = [];
  var statics : List<{ c : ClassType, f : ClassField }>;
  var packages : Map<String,Bool>;
  var forbidden : Map<String,Bool>;

  public function new(api){
    this.api = api;
    buf = new StringBuf();
    inits = new List();
    statics = new List();
    packages = new Map();
    forbidden = new Map();
    for(x in ["prototype", "__proto__", "constructor"]) forbidden.set(x, true);
    api.setTypeAccessor(getType);
  }

  function getType(t : Type){
    return switch(t){
      case TInst(c, _): getPath(c.get());
      case TEnum(e, _): getPath(e.get());
      case TAbstract(a,_): getPath(a.get());
      default: throw "wrong type: "+t;
    };
  }

  inline function print(str) buf.add(str);

  inline function println(str){ buf.add(str); buf.add('\n'); }

  inline function newline() buf.add(";\n");

  inline function genExpr(e) return api.generateStatement(e);

  inline function genVal(e) return api.generateValue(e);

  inline function field(p) return api.isKeyword(p) ? '["$p"]' : '.$p';

  inline function fieldInObj(p) return api.isKeyword(p) ? '"$p"' : p;

  function genPackage(p : Array<String>){
    var full = null;
    for(x in p){
      var prev = full;
      if(full == null) full = x else full += "." + x;
      if(!packages.exists(full)){
        packages.set(full, true);
        if(prev == null)
          // print('if(typeof $x==\'undefined\') $x = {}');
          print('var $x = {}');
        else{
          var p = prev + field(x);
          // print('if(!$p) $p = {}');
          print('$p = {}');
        }
        newline();
      }
    }
  }

  inline function getPath(t : BaseType){
    return (t.pack.length == 0) ? t.name : t.pack.join(".") + "." + t.name;
  }

  inline function checkFieldName(c : ClassType, f : ClassField){
    if(forbidden.exists(f.name))
      Context.error("The field " + f.name + " is not allowed in JS", c.pos);
  }

  function genClassField(c : ClassType, p : String, f : ClassField){
    // checkFieldName(c, f);
    // var field = field(f.name);
    // // print('$p.prototype$field = ');
    // // var e = f.expr();
    // // if(e == null)
    // //   print("null");
    // // else{
    // //   genVal(e);
    // // }
    // var e = f.expr();
    // if(e != null){
    //   print('$p.prototype$field = ');
    //   genVal(e);
    //   print(';\n');
    // }
    checkFieldName(c, f);
    var field = fieldInObj(f.name);
    // print('$p.prototype$field = ');
    // var e = f.expr();
    // if(e == null)
    //   print("null");
    // else{
    //   genVal(e);
    // }
    var e = f.expr();
    if(e != null){
      print('$field: ');
      print(genVal(e).replace('\n', '\n\t'));
      print('\n');
    }
  }

  function genStaticField(c : ClassType, p : String, f : ClassField){
    checkFieldName(c, f);
    var field = field(f.name);
    var e = f.expr();
    if(e != null) switch(f.kind){
      case FMethod(_):
        print('$p$field = ');
        print(genVal(e));
        print(';\n');
      default:
        statics.add({ c : c, f : f });
    }
  }

  function genClass(c : ClassType){
    if(c.init != null) inits.add(c.init);
    if(c.name == 'Math') print('Math.__name__ = ["Math"];\n');
    if(c.isExtern) return;
    genPackage(c.pack);
    api.setCurrentClass(c);
    var p = getPath(c);
    if(c.pack.length == 0) print('var ');
    print('$p = ');
    if(c.constructor != null)
      print(genVal(c.constructor.get().expr()));
    else
      print("function() { }");
    newline();
    print('$p.__name__ = [${p.split(".").map(api.quoteString).join(",")}]');
    newline();
    if(c.interfaces.length > 0){
      var me = this;
      var inter = c.interfaces.map(function(i) return me.getPath(i.t.get())).join(",");
      print('$p.__interfaces__ = [$inter];\n');
    }
    for(f in c.statics.get()) genStaticField(c, p, f);

    var fields = c.fields.get();
    var needProto = c.superClass != null || c.constructor != null || fields.length > 0;
    if(needProto){
      if(c.superClass != null){
        var psup = getPath(c.superClass.t.get());
        print('$p.__super__ = $psup;\n');
        print('$p.prototype = $$extend($psup.prototype,{\n');
      }
      else{
        print('$p.prototype = {\n');
      }
      var protoFieldCount = 0;
      for(f in fields){
        switch(f.kind){
        case FVar(r, _):
          if(r == AccResolve) continue;
        default:
        }
        // print('\ngenerating $c $p $f');
        if(f.expr() != null){
          print(protoFieldCount == 0 ? '\t' : '\t,');
          protoFieldCount++;
        }

        genClassField(c, p, f);
      }
      print(protoFieldCount == 0 ? '\t' : '\t,');
      print('__class__: $p\n');
      if(c.superClass != null){
        print('});\n');
      }
      else{
        print('};\n');
      }
    }
    var meta = api.buildMetaData(c);
    if(meta != null) metas.push('$p.__meta__ = ${genVal(meta)};\n');
  }

  function genEnum(e : EnumType){
    if(e.isExtern) return;
    genPackage(e.pack);
    var p = getPath(e);
    var names = p.split(".").map(api.quoteString).join(",");
    var constructs = e.names.map(api.quoteString).join(",");
    if(e.pack.length == 0) print('var ');
    print('$p = { __ename__ : [$names], __constructs__ : [$constructs] };\n');
    for(c in e.names){
      var c = e.constructs.get(c);
      var f = field(c.name);
      print('$p$f = ');
      switch(c.type){
      case TFun(args, _):
        var sargs = args.map(function(a) return a.name).join(",");
        print('function($sargs) { var $$x = ["${c.name}",${c.index},$sargs]; $$x.__enum__ = $p; $$x.toString = $$estr; return $$x; };\n');
      default:
        print("[" + api.quoteString(c.name) + "," + c.index + "];\n");
        print('$p$f.toString = $$estr;\n');
        print('$p$f.__enum__ = $p;\n');
      }
    }
    var meta = api.buildMetaData(e);
    if(meta != null) metas.push('$p.__meta__ = ${genVal(meta)};\n');
  }


  function genStaticValue(c : ClassType, cf : ClassField){
    var p = getPath(c);
    var f = field(cf.name);
    if(f == '.__meta__') return;
    print('$p$f = ');
    print(genVal(cf.expr()));
    print(';\n');
  }

  function genType(t : Type){
    switch(t){
      case TInst(c, _): genClass(c.get());
      case TEnum(r, _): genEnum(r.get());
      default:
    }
  }

  function printCode1(){
    print('(function () { "use strict";\n');
    print('var $$estr = function() { return js.Boot.__string_rec(this,\'\'); };\n');
    print('function $$extend(from, fields) {\n');
    print('\tfunction Inherit() {} Inherit.prototype = from; var proto = new Inherit();\n');
    print('\tfor (var name in fields) proto[name] = fields[name];\n');
    print('\tif( fields.toString !== Object.prototype.toString ) proto.toString = fields.toString;\n');
    print('\treturn proto;\n');
    print('}\n');
  }

  function printCode2(){
    print("function $iterator(o) { if( o instanceof Array ) return function() { return HxOverrides.iter(o); }; return typeof(o.iterator) == 'function' ? $bind(o,o.iterator) : o.iterator; }\n");
    print("var $_, $fid = 0;\n");
    print("function $bind(o,m) { if( m == null ) return null; if( m.__id__ == null ) m.__id__ = $fid++; var f; if( o.hx__closures__ == null ) o.hx__closures__ = {}; else f = o.hx__closures__[m.__id__]; if( f == null ) { f = function(){ return f.method.apply(f.scope, arguments); }; f.scope = o; f.method = m; o.hx__closures__[m.__id__] = f; } return f; }\n");
  }

  public function generate(out, types){
    printCode1();

    for(t in api.types) genType(t);

    printCode2();

    for(e in inits){
      var s = genExpr(e);
      if(s != ''){
        if(s.charCodeAt(0) == '{'.code && s.charCodeAt(1) == '\n'.code && s.charCodeAt(s.length-1) == '}'.code){
          print(s.substr(3, s.length - 4).replace('\n\t', '\n'));
        }
        else{
          print(s+';\n');
        }
      }
    }

    for(meta in metas) print(meta);

    for(s in statics) genStaticValue(s.c,s.f);

    if(api.main != null){
      print(genExpr(api.main));
      print(';\n');
    }
    print('})();\n');
    sys.io.File.saveContent(out, buf.toString());
  }

  #if macro
  public static function use(){
    Compiler.setCustomJSGenerator(function(api) new ExampleGen(api).generate(api.outputFile, api.types));
  }
  #end

}
