use super::*;

/// The function macro (bound to `fn`) takes a function form that has the following elements:
/// 1. The `fn` symbol,
/// 2. An optional symbol providing the function's name for recursive calls,
/// 3. A list of arguments,
/// 4. Zero or more _silent_ expressions, that are evaluated for their side-effects, and
/// 5. A last expression that is evaluated to produce the return value.
///
/// ```
/// use risp::*;
/// use risp::builtins::*;
/// let mut ctx = BasicStaticContext::new();
/// install_builtins(&mut ctx);
/// let form = read("(fn (x) x)").unwrap()[0].clone();
/// let compiled = compile(form, &ctx).unwrap();
/// assert_eq!(compiled.call(&vec![RispValue::Int(2)].into_iter().collect()),
///            Ok(RispValue::Int(2)));
/// ```
pub fn fn_macro(form: RispValue) -> Result<RispValue, CompilationError> {
    let mut i = form.iter();
    i.next(); // Consume fn symbol
    let formal_args = i.next().ok_or(CompilationError::ArityMismatch(1, 0))?.clone();
    let body = i.next().ok_or(CompilationError::ArityMismatch(2, 1))?.clone();
    Ok(RispValue::Fn(RispFunc::new(Arc::new(move |act_args| {
        let bindings = act_args.match_pattern(&formal_args).ok_or(CompilationError::ArityMismatch(0,0))?;
        body.eval(&DerivedDynamicContext::new(&BasicDynamicContext::new(), bindings))
    }))))
}


/// Installs all builtins to the given static context
pub fn install_builtins(ctx: &mut BasicStaticContext) {
    ctx.define_macro(String::from("fn"), Box::new(fn_macro));
}
