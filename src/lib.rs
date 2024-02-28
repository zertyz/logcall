// Copyright 2020 TiKV Project Authors. Licensed under Apache-2.0.

#![doc = include_str!("../README.md")]
#![recursion_limit = "256"]
// Instrumenting the async fn is not as straight forward as expected because `async_trait` rewrites `async fn`
// into a normal fn which returns `Box<impl Future>`, and this stops the macro from distinguishing `async fn` from `fn`.
// The following code reused the `async_trait` probes from [tokio-tracing](https://github.com/tokio-rs/tracing/blob/6a61897a5e834988ad9ac709e28c93c4dbf29116/tracing-attributes/src/expand.rs).

extern crate proc_macro;

#[macro_use]
extern crate proc_macro_error;

use proc_macro2::{Span, TokenStream};
use quote::{quote_spanned, ToTokens};
use syn::spanned::Spanned;
use syn::Ident;
use syn::*;
use syn::parse::{Parse, ParseStream};
use syn::punctuated::Punctuated;
use syn::token::Comma;

/// Contains the internal representation of this proc-macro arguments.
/// See [MacroArgs::parse()] for more info.
struct MacroArgs {
    /// If `None`, no function ingress logging will be done -- as determined by the attributes parameters
    log_ingress_level: Option<String>,
    /// If `None`, no function egress logging will be done
    log_egress_args: Option<LogEgressArgs>,
    /// If `None`, params for the function won't be logged.
    /// If `Some`, parameters not in the list will be logged (through the `Debug` trait),
    /// either in ingress, egress or both.
    /// If the list is `Some([])` (empty list), all the parameters will be logged.
    params: Option<Vec<String>>,
}

/// Arguments for the "log on the egress of a function" feature
enum LogEgressArgs {
    /// Egress log info for a non-fallible function
    Simple {
        level: String,
    },
    /// Egress log info for a fallible function
    Result {
        ok_level: Option<String>,
        err_level: Option<String>,
    },
}

impl Parse for MacroArgs {

    /// `args` comes from one of the forms bellow
    ///    1) LEVEL -- logs only the output of a function, when leaving the function -- without any distinction regarding if it is fallible or not
    ///    2) ingress=LEVEL -- logs only the inputs of a function call, on function ingress
    ///    3) ingress=LEVEL, egress=LEVEL -- same as #1 & #2 combined
    ///    4) LEVEL, skip=[list]) -- same as #1, logging both the return value and the inputs when leaving the function, but excludes the parameter names in [list] from the `debug` serialization
    ///    5) ingress=LEVEL, skip=[list] -- same as #2, but excludes the identifiers in [list] from the `debug` serialization
    ///    6) ingress=LEVEL, egress=LEVEL, skip=[list] -- same as #3, but excludes the identifiers in [list] from the `debug` serialization
    ///    7) ok=LEVEL, err=LEVEL -- logs only the output of a fallible function -- either `Ok` or `Err` -- in their designated levels
    ///    8) ok=LEVEL -- same as #7, but refrains from logging results that failed in `Err`
    ///    9) err=LEVEL -- same as #7, but refrains from logging results that succeeded in `Ok`
    ///   10) ingress=LEVEL, ok=LEVEL, err=LEVEL -- same as #3, but for a fallible function -- with each result variant logged at their designated levels
    ///   11) ingress=LEVEL, ok=LEVEL -- same as #8, additionally logging all the inputs on both ingress & egress
    ///   12) ingress=LEVEL, err=LEVEL -- same as #9, additionally logging all the inputs on both ingress & egress
    ///   13) ingress=LEVEL, ok=LEVEL, err=LEVEL, skip=[list] -- same as #10, but excludes the parameters in [list] from the `debug` serialization on ingress & egress
    ///   14) ingress=LEVEL, ok=LEVEL, skip=[list] -- same as #11, but excludes the parameters in [list] from the `debug` serialization
    ///   15) ingress=LEVEL, err=LEVEL, skip=[list] -- same as #12, but excludes the parameters in [list] from the `debug` serialization
    ///   16) [ok=LEVEL, ][err=LEVEL, ]skip=[list] -- error: if `skip` is present (meaning logging the inputs is activated), either `ingress`, `egress` or the legacy egress LEVEL literal must also be present
    ///   17) LEVEL, [*, ]egress=LEVEL -- error: The legacy egress level and the new "egress=LEVEL" form cannot be specified concurrently
    ///   18) <empty> -- error: when annotating with #[logcall(...)], parameters should be provided, otherwise the annotation would have no effect
    /// where:
    ///   LEVEL: "trace"|"debug"|"info"|"warn"|"error"
    ///   [list]: a list of identifiers, such as self,param_3,...
    /// note:
    ///   All named parameters -- "ingress", "egress", "err", "ok" & "skip" -- may come in any order.
    ///   There is a requirement, 'though, that the literal parameter "LEVEL" must be the first one, if present
    fn parse(args: ParseStream) -> Result<MacroArgs> {

        fn trim_quotes(maybe_quoted: &str) -> String {
            maybe_quoted.trim_start_matches('"').trim_end_matches('"').to_string()
        }

        // match & consume the optional legacy output "level" literal
        let legacy_output = args.parse::<syn::Lit>().ok()
            .map(|literal| trim_quotes(&literal.to_token_stream().to_string()));
        // consumes the "," between the legacy and "name=val" list that may, possibly, follow
        args.parse::<Token![,]>().ok();

        // from this point on, all other acceptable parameters will be in the form "name=val<, ...>"
        let mut ok = None;
        let mut err = None;
        let mut ingress = None;
        let mut egress = None;
        let mut skip = None;
        let name_values = Punctuated::<MetaNameValue, Token![,]>::parse_terminated(args)?;
        for name_value in &name_values {
            let Some(name) =
                name_value.path.get_ident().map(|ident| ident.to_string())
            else {
                panic!("VALUE IS NOT AN IDENTIFIER");
            };

            // treat the optional skip=array parameter -- where `array` a list of identifiers: skip=[identifiers_list];
            if name.as_str() == "skip" {
                let Expr::Array(expr_array) = name_value.value.clone() else {
                    panic!("`skip` parameter, if present, should be an array of identifiers: skip=[a,b,c,...]");
                };
                for pair in expr_array.elems.pairs() {
                    let ident = pair.value().to_token_stream().to_token_stream().to_string();
                    skip.get_or_insert_with(|| Vec::new())
                        .push(ident);
                }
                continue;
            }

            // treat name=literal values
            let Expr::Lit(ref literal_value) =
                name_value.value
            else {
                panic!("VALUE IS NOT A LITERAL");
            };
            let value = trim_quotes(&literal_value.lit.to_token_stream().to_string());
            match name.as_str() {
                "err" => err.replace(value),
                "ok" => ok.replace(value),
                "ingress" => ingress.replace(value),
                "egress" => egress.replace(value),
                _ => panic!("Unknown parameter in the `name=value` form: {}={}", name, value),
            };
        }

        // parameters set checks
        ////////////////////////

        // ingress logging rules
        if ingress.is_some() && skip.is_none() {
            // if "logging on function ingress" is enabled, logging the parameters is also enabled
            skip.replace(Vec::new());
        }

        // egress logging rules
        let log_egress_args = if let Some(simple_output_level) = egress {
            Some(LogEgressArgs::Simple { level: simple_output_level })
        } else if let Some(simple_output_level) = legacy_output {
            Some(LogEgressArgs::Simple { level: simple_output_level })
        } else {
            // result output?
            if ok.is_none() && err.is_none() {
                None
            } else {
                Some(LogEgressArgs::Result { ok_level: ok, err_level: err })
            }
        };

        assert!(ingress.is_some() || log_egress_args.is_some(), "`logcall`: when annotating with #[logcall(...)], ingress/egress log level parameters should be provided, otherwise the annotation would have no effect");

        Ok(MacroArgs {
            log_ingress_level: ingress,
            log_egress_args,
            params: skip,
        })

    }
}

/// An attribute macro that logs the function return value.
#[proc_macro_attribute]
#[proc_macro_error]
pub fn logcall(
    macro_args_tokens: proc_macro::TokenStream,
    fn_tokens: proc_macro::TokenStream,
) -> proc_macro::TokenStream {
    let fn_item = syn::parse_macro_input!(fn_tokens as ItemFn);
    let macro_args = syn::parse_macro_input!(macro_args_tokens as MacroArgs);

    let fn_name = fn_item.sig.ident.to_string();
    let fn_args = fn_item
        .sig
        .inputs
        .iter()
        .cloned()
        .map(|arg| match arg {
            FnArg::Receiver(arg) => arg.self_token.into(),
            FnArg::Typed(pat_type) => {
                if let Pat::Ident(ident) = *pat_type.pat {
                    ident.ident
                } else {
                    panic!("Unknown parameter declaration for {:?}", pat_type);
                }
            }
        })
        .collect();

    // check for async_trait-like patterns in the block, and instrument
    // the future instead of the wrapper
    let func_body = if let Some(internal_fun) =
        get_async_trait_info(&fn_item.block, fn_item.sig.asyncness.is_some())
    {
        // let's rewrite some statements!
        match internal_fun.kind {
            // async-trait <= 0.1.43
            AsyncTraitKind::Function(_) => {
                unimplemented!(
                    "Please upgrade the crate `async-trait` to a version higher than 0.1.44"
                )
            }
            // async-trait >= 0.1.44
            AsyncTraitKind::Async(async_expr) => {
                // fallback if we couldn't find the '__async_trait' binding, might be
                // useful for crates exhibiting the same behaviors as async-trait
                let instrumented_block = gen_egress_block(
                    &async_expr.block,
                    true,
                    false,
                    &fn_name,
                    fn_args,
                    macro_args,
                );
                let async_attrs = &async_expr.attrs;
                quote! {
                    Box::pin(#(#async_attrs) * #instrumented_block )
                }
            }
        }
    } else {
        gen_egress_block(
            &fn_item.block,
            fn_item.sig.asyncness.is_some(),
            fn_item.sig.asyncness.is_some(),
            &fn_name,
            fn_args,
            macro_args,
        )
    };

    let ItemFn {
        attrs, vis, sig, ..
    } = fn_item;

    let Signature {
        output: return_type,
        inputs: params,
        unsafety,
        constness,
        abi,
        ident,
        asyncness,
        generics:
            Generics {
                params: gen_params,
                where_clause,
                ..
            },
        ..
    } = sig;

    quote::quote!(
        #(#attrs) *
        #vis #constness #unsafety #asyncness #abi fn #ident<#gen_params>(#params) #return_type
        #where_clause
        {
            #func_body
        }
    )
    .into()
}

/// Instrument when exiting a block
fn gen_egress_block(
    block: &Block,
    async_context: bool,
    async_keyword: bool,
    fn_name: &str,
    fn_args: Vec<Ident>,
    macro_args: MacroArgs,
) -> proc_macro2::TokenStream {
    match macro_args.log_egress_args.unwrap() {
        LogEgressArgs::Simple { level } => {
            // Generate the instrumented function body.
            // If the function is an `async fn`, this will wrap it in an async block.
            if async_context {
                let log = gen_egress_log(&level, fn_name, &fn_args, &macro_args.params, "__ret_value");
                let block = quote_spanned!(block.span()=>
                    async move {
                        let __ret_value = async move { #block }.await;
                        #log;
                        __ret_value
                    }
                );

                if async_keyword {
                    quote_spanned!(block.span()=>
                        #block.await
                    )
                } else {
                    block
                }
            } else {
                let log = gen_egress_log(&level, fn_name, &fn_args, &macro_args.params, "__ret_value");
                quote_spanned!(block.span()=>
                    #[allow(unknown_lints)]
                    #[allow(clippy::redundant_closure_call)]
                    let __ret_value = (move || #block)();
                    #log;
                    __ret_value
                )
            }
        }
        LogEgressArgs::Result {
            ok_level,
            err_level,
        } => {
            let ok_arm = if let Some(ok_level) = ok_level {
                let log_ok = gen_egress_log(&ok_level, fn_name, &fn_args, &macro_args.params, "__ret_value");
                quote_spanned!(block.span()=>
                    __ret_value@Ok(_) => {
                        #log_ok;
                        __ret_value
                    }
                )
            } else {
                quote_spanned!(block.span()=>
                    Ok(__ret_value) => Ok(__ret_value),
                )
            };
            let err_arm = if let Some(err_level) = err_level {
                let log_err = gen_egress_log(&err_level, fn_name, &fn_args, &macro_args.params, "__ret_value");
                quote_spanned!(block.span()=>
                    __ret_value@Err(_) => {
                        #log_err;
                        __ret_value
                    }
                )
            } else {
                quote_spanned!(block.span()=>
                    Err(__ret_value) => Err(__ret_value),
                )
            };

            // Generate the instrumented function body.
            // If the function is an `async fn`, this will wrap it in an async block.
            if async_context {
                let block = quote_spanned!(block.span()=>
                    async move {
                        let __ret_value = async move { #block }.await;
                        match __ret_value {
                            #ok_arm
                            #err_arm
                        }
                    }
                );

                if async_keyword {
                    quote_spanned!(block.span()=>
                        #block.await
                    )
                } else {
                    block
                }
            } else {
                quote_spanned!(block.span()=>
                    #[allow(unknown_lints)]
                    #[allow(clippy::redundant_closure_call)]
                    let __ret_value = (move || #block)();
                    match __ret_value {
                        #ok_arm
                        #err_arm
                    }
                )
            }
        }
    }
}

fn gen_ingress_log(level: &str, fn_name: &str, return_value: &str) -> proc_macro2::TokenStream {
    let level = level.to_lowercase();
    if !["error", "warn", "info", "debug", "trace"].contains(&level.as_str()) {
        abort_call_site!("unknown log level");
    }
    let level: Ident = Ident::new(&level, Span::call_site());
    let return_value: Ident = Ident::new(return_value, Span::call_site());
    quote!(
        log::#level! ("{}() => {:?}", #fn_name, &#return_value)
    )
}

fn gen_egress_log(level: &str, fn_name: &str, param_names: &Vec<Ident>, params_to_skip: &Option<Vec<String>>, return_value: &str) -> TokenStream {
    let level = level.to_lowercase();
    if !["error", "warn", "info", "debug", "trace"].contains(&level.as_str()) {
        abort_call_site!("unknown log level");
    }
    let level: Ident = Ident::new(&level, Span::call_site());
    let return_value: Ident = Ident::new(return_value, Span::call_site());
    let mut fmt = String::from("{}(");
    let (input_params, input_values) = build_input_format_arguments(param_names, params_to_skip.as_ref().unwrap_or(&param_names.iter().map(|ident| ident.to_string()).collect()));
    fmt.push_str(&input_params);
    fmt.push_str(") => {:?}");
// panic!("FORMAT: #fmt: {}, #fn_name: {}, #input_values: {:?}, &#return_value: {}", fmt, fn_name, input_values, &return_value);
    quote!(
        ::log::#level! (#fmt, #fn_name, #input_values /*notice the missing comma*/ &#return_value)
    )
}

/// Builds the arguments to be used in `format!()`.
/// Returns: (format_placeholders, format_values)
/// Caveat: `format_values` is a `TokenStream` with an extra comma, for coding simplicity -- meaning no comma should be placed after it, when using it in `quote!()`
fn build_input_format_arguments(param_idents: &Vec<Ident>, to_skip: &Vec<String>)
                                -> (/*format_placeholders: */String, /*format_values: */TokenStream) {
    let format_placeholders = param_idents.iter().enumerate()
        .map(|(param_index, param_ident)| {
            let param_name = param_ident.to_string();
            let placeholder = if to_skip.contains(&param_name) {
                "<skipped>"
            } else {
                // the param will be serialized with `debug`
                "{:?}"
            };
            let placeholder_separator = if param_index>0 {", "} else {""};
            let format_placeholder = format!("{placeholder_separator}{param_name}: {placeholder}");
            format_placeholder
        })
        .collect();
    let format_values: Punctuated<Ident, Comma> = param_idents.iter().cloned()
        .filter(|param_ident| !to_skip.contains(&param_ident.to_string()))
        .collect();
    let format_values = if format_values.len() == 0 {
        format_values.to_token_stream()
    } else {
        quote!(#format_values, /* notice the leading comma */)
    };
    (format_placeholders, format_values)
}

enum AsyncTraitKind<'a> {
    // old construction. Contains the function
    Function(&'a ItemFn),
    // new construction. Contains a reference to the async block
    Async(&'a ExprAsync),
}

struct AsyncTraitInfo<'a> {
    // statement that must be patched
    _source_stmt: &'a Stmt,
    kind: AsyncTraitKind<'a>,
}

// Get the AST of the inner function we need to hook, if it was generated
// by async-trait.
// When we are given a function annotated by async-trait, that function
// is only a placeholder that returns a pinned future containing the
// user logic, and it is that pinned future that needs to be instrumented.
// Were we to instrument its parent, we would only collect information
// regarding the allocation of that future, and not its own span of execution.
// Depending on the version of async-trait, we inspect the block of the function
// to find if it matches the pattern
// `async fn foo<...>(...) {...}; Box::pin(foo<...>(...))` (<=0.1.43), or if
// it matches `Box::pin(async move { ... }) (>=0.1.44). We the return the
// statement that must be instrumented, along with some other informations.
// 'gen_body' will then be able to use that information to instrument the
// proper function/future.
// (this follows the approach suggested in
// https://github.com/dtolnay/async-trait/issues/45#issuecomment-571245673)
fn get_async_trait_info(block: &Block, block_is_async: bool) -> Option<AsyncTraitInfo<'_>> {
    // are we in an async context? If yes, this isn't a async_trait-like pattern
    if block_is_async {
        return None;
    }

    // list of async functions declared inside the block
    let inside_funs = block.stmts.iter().filter_map(|stmt| {
        if let Stmt::Item(Item::Fn(fun)) = &stmt {
            // If the function is async, this is a candidate
            if fun.sig.asyncness.is_some() {
                return Some((stmt, fun));
            }
        }
        None
    });

    // last expression of the block (it determines the return value
    // of the block, so that if we are working on a function whose
    // `trait` or `impl` declaration is annotated by async_trait,
    // this is quite likely the point where the future is pinned)
    let (last_expr_stmt, last_expr) = block.stmts.iter().rev().find_map(|stmt| {
        if let Stmt::Expr(expr, _token) = stmt {
            Some((stmt, expr))
        } else {
            None
        }
    })?;

    // is the last expression a function call?
    let (outside_func, outside_args) = match last_expr {
        Expr::Call(ExprCall { func, args, .. }) => (func, args),
        _ => return None,
    };

    // is it a call to `Box::pin()`?
    let path = match outside_func.as_ref() {
        Expr::Path(path) => &path.path,
        _ => return None,
    };
    if !path_to_string(path).ends_with("Box::pin") {
        return None;
    }

    // Does the call take an argument? If it doesn't,
    // it's not gonna compile anyway, but that's no reason
    // to (try to) perform an out of bounds access
    if outside_args.is_empty() {
        return None;
    }

    // Is the argument to Box::pin an async block that
    // captures its arguments?
    if let Expr::Async(async_expr) = &outside_args[0] {
        // check that the move 'keyword' is present
        async_expr.capture?;

        return Some(AsyncTraitInfo {
            _source_stmt: last_expr_stmt,
            kind: AsyncTraitKind::Async(async_expr),
        });
    }

    // Is the argument to Box::pin a function call itself?
    let func = match &outside_args[0] {
        Expr::Call(ExprCall { func, .. }) => func,
        _ => return None,
    };

    // "stringify" the path of the function called
    let func_name = match **func {
        Expr::Path(ref func_path) => path_to_string(&func_path.path),
        _ => return None,
    };

    // Was that function defined inside of the current block?
    // If so, retrieve the statement where it was declared and the function itself
    let (stmt_func_declaration, func) = inside_funs
        .into_iter()
        .find(|(_, fun)| fun.sig.ident == func_name)?;

    Some(AsyncTraitInfo {
        _source_stmt: stmt_func_declaration,
        kind: AsyncTraitKind::Function(func),
    })
}

// Return a path as a String
fn path_to_string(path: &Path) -> String {
    use std::fmt::Write;
    // some heuristic to prevent too many allocations
    let mut res = String::with_capacity(path.segments.len() * 5);
    for i in 0..path.segments.len() {
        write!(res, "{}", path.segments[i].ident).expect("writing to a String should never fail");
        if i < path.segments.len() - 1 {
            res.push_str("::");
        }
    }
    res
}
