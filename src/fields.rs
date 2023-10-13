use darling::ast::{Fields, Style};
use proc_macro2::TokenStream;
use quote::{format_ident, quote, ToTokens};

/// Utility macro to implement [FieldInfo]
#[macro_export]
macro_rules! field_info {
    ($f:path) => {
        impl $crate::FieldInfo for $f {
            fn ident(&self) -> &Option<syn::Ident> {
                &self.ident
            }

            fn vis(&self) -> &syn::Visibility {
                &self.vis
            }

            fn ty(&self) -> &syn::Type {
                &self.ty
            }
        }
    };
}

/// Trait to retrieve fields' properties
pub trait FieldInfo {
    /// Retrieves the identifier of the passed-in field, or [None] for tuple fields
    fn ident(&self) -> &Option<syn::Ident>;
    /// Retrieves the visibility of the passed-in field
    fn vis(&self) -> &syn::Visibility;
    /// Retrieves the type of the passed-in field
    fn ty(&self) -> &syn::Type;
    /// Retrieves the ident of the field or a `v_{ix}` ident based on the field index
    fn as_ident(&self, ix: usize) -> syn::Ident {
        self.ident().clone().unwrap_or_else(|| format_ident!("v_{ix}"))
    }
}

/// Utility struct to work with [Fields]
pub struct FieldsHelper<'f, T: FieldInfo> {
    fields: Fields<&'f T>,
    filter: Option<Box<dyn Fn(usize, &T) -> bool + 'f>>,
    attributes: Option<Box<dyn Fn(usize, &T) -> Option<TokenStream> + 'f>>,
    include_default: Vec<TokenStream>,
    include_all_default: bool,
    ignore_extra: Vec<syn::Ident>,
    ignore_all_extra: bool,
    include_visibility: bool,
    left_collector: Option<Box<dyn FnMut(usize, &T) -> TokenStream + 'f>>,
    right_collector: Option<Box<dyn FnMut(usize, &T) -> TokenStream + 'f>>,
}

impl<'f, T: FieldInfo> FieldsHelper<'f, T> {
    /// Builds a new [FieldsHelper]
    pub fn new(fields: &'f Fields<T>) -> Self {
        Self {
            fields: fields.as_ref(),
            filter: None,
            attributes: None,
            include_default: Vec::new(),
            include_all_default: false,
            ignore_extra: Vec::new(),
            ignore_all_extra: false,
            include_visibility: false,
            left_collector: None,
            right_collector: None,
        }
    }

    /// Remove all fields `f` for which `predicate(&f)` returns `false`.
    /// This method operates in place, visiting each element exactly once in the
    /// original order, and preserves the order of the retained elements.
    pub fn filtering<P>(mut self, predicate: P) -> Self
    where
        P: Fn(usize, &T) -> bool + 'f,
    {
        self.filter = Some(Box::new(predicate));
        self
    }

    /// Adds an arbitrary number of attributes to each field.
    pub fn with_attributes<P>(mut self, predicate: P) -> Self
    where
        P: Fn(usize, &T) -> Option<TokenStream> + 'f,
    {
        self.attributes = Some(Box::new(predicate));
        self
    }

    /// Includes default fields by including `, field1: Default::default() , field2: Default::default()` at the end.
    ///
    /// It's only used on named fields, but ignored for tuples.
    pub fn include_default<'a>(mut self, include_default: impl IntoIterator<Item = &'a syn::Ident>) -> Self {
        let mut include_default = include_default
            .into_iter()
            .map(|field| quote!(#field: Default::default()))
            .collect::<Vec<_>>();
        self.include_default.append(&mut include_default);
        self
    }

    /// Includes default fields by including `, field1: expr1 , field2: expr2` at the end.
    ///
    /// It's only used on named fields, but ignored for tuples.
    pub fn include_default_with<'a>(
        mut self,
        include_default: impl IntoIterator<Item = (&'a syn::Ident, impl ToTokens)>,
    ) -> Self {
        let mut include_default = include_default
            .into_iter()
            .map(|(field, expr)| quote!(#field: #expr))
            .collect::<Vec<_>>();
        self.include_default.append(&mut include_default);
        self
    }

    /// Wether to include `, ..Default::default()` at the end or not, defaults to `false`.
    pub fn include_all_default(mut self, include_all_default: bool) -> Self {
        self.include_all_default = include_all_default;
        self
    }

    /// Ignore extra fields by including `, field1: _ , field2: _` at the end.
    ///
    /// It's only used on named fields, but ignored for tuples.
    pub fn ignore_extra<'a>(mut self, ignore_extra: impl IntoIterator<Item = &'a syn::Ident>) -> Self {
        let mut ignore_extra = ignore_extra.into_iter().cloned().collect::<Vec<_>>();
        self.ignore_extra.append(&mut ignore_extra);
        self
    }

    /// Wether to include `, ..` at the end or not, defaults to `false`.
    pub fn ignore_all_extra(mut self, ignore_all_extra: bool) -> Self {
        self.ignore_all_extra = ignore_all_extra;
        self
    }

    /// Wether to include the visibility at the beginning or not, defaults to `false`.
    pub fn include_visibility(mut self, include_visibility: bool) -> Self {
        self.include_visibility = include_visibility;
        self
    }

    /// Specifies the left collector. It's only used with named fields.
    ///
    /// Defaults to `FieldsCollector::ident`
    pub fn left_collector<C>(mut self, left_collector: C) -> Self
    where
        C: FnMut(usize, &T) -> TokenStream + 'f,
    {
        self.left_collector = Some(Box::new(left_collector));
        self
    }

    /// Specifies the right collector.
    ///
    /// Defaults to `FieldsCollector::ty`
    pub fn right_collector<C>(mut self, right_collector: C) -> Self
    where
        C: FnMut(usize, &T) -> TokenStream + 'f,
    {
        self.right_collector = Some(Box::new(right_collector));
        self
    }

    /// Checks if there's no fields
    pub fn is_empty(&self) -> bool {
        if self.fields.is_empty() {
            true
        } else if let Some(filter_fn) = &self.filter {
            self.fields
                .iter()
                .enumerate()
                .filter(|&(ix, f)| filter_fn(ix, f))
                .collect::<Vec<_>>()
                .is_empty()
        } else {
            false
        }
    }

    /// Takes the inner fields
    pub fn into_vec(self) -> Vec<&'f T> {
        self.fields.fields
    }

    /// Collects the fields.
    ///
    /// # Examples
    /// If using the default collectors on a Struct:
    /// ``` ignore
    /// {
    ///     field_1: String,
    ///     field_2: i32,
    /// }
    /// ```
    ///
    /// If using `FieldsCollector::ident` right collector on a Struct:
    /// ``` ignore
    /// {
    ///     field_1: field_1,
    ///     field_2: field_2,
    /// }
    /// ```
    pub fn collect(mut self) -> TokenStream {
        let mut tokens = TokenStream::new();
        match self.fields.style {
            Style::Unit => (),
            Style::Tuple => {
                let mut right_collector = self.right_collector.unwrap_or_else(|| Box::new(FieldsCollector::ty));

                let fields = self
                    .fields
                    .into_iter()
                    .enumerate()
                    .filter(|&(ix, f)| {
                        if let Some(filter_fn) = &mut self.filter {
                            filter_fn(ix, f)
                        } else {
                            true
                        }
                    })
                    .map(|(ix, f)| {
                        let vis = f.vis();
                        let collected_field = right_collector(ix, f);
                        let attrs = if let Some(attrs_fn) = &mut self.attributes {
                            attrs_fn(ix, f)
                        } else {
                            None
                        }
                        .unwrap_or_default();
                        if self.include_visibility {
                            quote!( #attrs #vis #collected_field )
                        } else {
                            quote!( #attrs #collected_field )
                        }
                    });
                if self.include_all_default {
                    quote!( (#( #fields ),* , ..Default::default() ) ).to_tokens(&mut tokens);
                } else if self.ignore_all_extra {
                    quote!( (#( #fields ),* , .. ) ).to_tokens(&mut tokens);
                } else {
                    quote!( (#( #fields ),* ) ).to_tokens(&mut tokens);
                }
            }
            Style::Struct => {
                let mut left_collector = self.left_collector.unwrap_or_else(|| Box::new(FieldsCollector::ident));
                let mut right_collector = self.right_collector.unwrap_or_else(|| Box::new(FieldsCollector::ty));

                let mut fields = self
                    .fields
                    .into_iter()
                    .enumerate()
                    .filter(|&(ix, f)| {
                        if let Some(filter_fn) = &mut self.filter {
                            filter_fn(ix, f)
                        } else {
                            true
                        }
                    })
                    .map(|(ix, f)| {
                        let id = left_collector(ix, f);
                        let vis = f.vis();
                        let collected_field = right_collector(ix, f);
                        let attrs = if let Some(attrs_fn) = &mut self.attributes {
                            attrs_fn(ix, f)
                        } else {
                            None
                        }
                        .unwrap_or_default();
                        if self.include_visibility {
                            quote!(
                                #attrs
                                #vis #id: #collected_field
                            )
                        } else {
                            quote!(
                                #attrs
                                #id: #collected_field
                            )
                        }
                    })
                    .collect::<Vec<_>>();

                fields.append(&mut self.include_default);

                let mut ignore_extra = self
                    .ignore_extra
                    .into_iter()
                    .map(|field| quote!(#field: _))
                    .collect::<Vec<_>>();
                fields.append(&mut ignore_extra);

                if self.include_all_default {
                    quote!( {#( #fields ),* , ..Default::default() } ).to_tokens(&mut tokens);
                } else if self.ignore_all_extra {
                    quote!( {#( #fields ),* , .. } ).to_tokens(&mut tokens);
                } else {
                    quote!( {#( #fields ),* } ).to_tokens(&mut tokens);
                }
            }
        }
        tokens
    }
}

/// Utility struct with common collectors for [FieldsHelper]
pub struct FieldsCollector;
impl FieldsCollector {
    // Collects just the type of the field
    pub fn ty<T: FieldInfo>(_ix: usize, t: &T) -> TokenStream {
        let ty = t.ty();

        quote!(#ty)
    }

    // Collects just the ident of the field
    pub fn ident<T: FieldInfo>(ix: usize, t: &T) -> TokenStream {
        let ident = t.as_ident(ix);

        quote!(#ident)
    }

    // Collects just `Default::default()`
    pub fn default<T: FieldInfo>(_ix: usize, _t: &T) -> TokenStream {
        quote!(Default::default())
    }

    // Collects just `_`
    pub fn ignore<T: FieldInfo>(_ix: usize, _t: &T) -> TokenStream {
        quote!(_)
    }
}

#[cfg(test)]
mod tests {
    use darling::FromField;
    use quote::quote;
    use syn::Result;

    use super::*;

    #[derive(FromField, Clone)]
    #[darling(attributes(tst))]
    struct FieldReceiver {
        /// The identifier of the passed-in field, or [None] for tuple fields
        ident: Option<syn::Ident>,
        /// The visibility of the passed-in field
        vis: syn::Visibility,
        /// The type of the passed-in field
        ty: syn::Type,

        /// Whether to skip
        #[darling(default)]
        skip: bool,
    }
    field_info!(FieldReceiver);

    #[test]
    fn test_field_helper_named() -> Result<()> {
        let fields: syn::FieldsNamed = syn::parse2(quote!({
            pub field_1: String,
            #[tst(skip)]
            pub field_2: i32,
            pub field_3: i64,
            field_4: bool,
        }))?;
        let fields = Fields::<FieldReceiver>::try_from(&syn::Fields::Named(fields))?;

        let collected = FieldsHelper::new(&fields).filtering(|_ix, f| !f.skip).collect();
        #[rustfmt::skip]
        let expected = quote!({
            field_1: String,
            field_3: i64,
            field_4: bool
        });

        assert_eq!(collected.to_string(), expected.to_string());

        let collected = FieldsHelper::new(&fields).include_visibility(true).collect();
        #[rustfmt::skip]
        let expected = quote!({
            pub field_1: String,
            pub field_2: i32,
            pub field_3: i64,
            field_4: bool
        });

        assert_eq!(collected.to_string(), expected.to_string());

        let collected = FieldsHelper::new(&fields)
            .filtering(|_ix, f| !f.skip)
            .include_all_default(true)
            .right_collector(FieldsCollector::ident)
            .collect();
        #[rustfmt::skip]
        let expected = quote!({
            field_1: field_1,
            field_3: field_3,
            field_4: field_4,
            .. Default::default()
        });

        assert_eq!(collected.to_string(), expected.to_string());

        let collected = FieldsHelper::new(&fields)
            .filtering(|_ix, f| !f.skip)
            .ignore_all_extra(true)
            .right_collector(FieldsCollector::ident)
            .collect();
        #[rustfmt::skip]
        let expected = quote!({
            field_1: field_1,
            field_3: field_3,
            field_4: field_4,
            ..
        });

        assert_eq!(collected.to_string(), expected.to_string());

        let collected = FieldsHelper::new(&fields)
            .with_attributes(|_ix, f| if f.skip { Some(quote!(#[skipped])) } else { None })
            .collect();
        #[rustfmt::skip]
        let expected = quote!({
            field_1: String,
            #[skipped]
            field_2: i32,
            field_3: i64,
            field_4: bool
        });

        assert_eq!(collected.to_string(), expected.to_string());

        let collected = FieldsHelper::new(&fields)
            .filtering(|_ix, f| !f.skip)
            .right_collector(FieldsCollector::ident)
            .include_default(fields.fields.iter().filter(|f| f.skip).filter_map(|f| f.ident.as_ref()))
            .collect();
        #[rustfmt::skip]
        let expected = quote!({
            field_1: field_1,
            field_3: field_3,
            field_4: field_4,
            field_2: Default::default()
        });

        assert_eq!(collected.to_string(), expected.to_string());

        let collected = FieldsHelper::new(&fields)
            .filtering(|_ix, f| !f.skip)
            .right_collector(FieldsCollector::ident)
            .include_default_with(
                fields
                    .fields
                    .iter()
                    .filter(|f| f.skip)
                    .filter_map(|f| f.ident.as_ref().map(|ident| (ident, quote!(5)))),
            )
            .collect();
        #[rustfmt::skip]
        let expected = quote!({
            field_1: field_1,
            field_3: field_3,
            field_4: field_4,
            field_2: 5
        });

        assert_eq!(collected.to_string(), expected.to_string());

        Ok(())
    }

    #[test]
    fn test_field_helper_unnamed() -> Result<()> {
        let fields: syn::FieldsUnnamed = syn::parse2(quote! {(
            pub String,
            #[tst(skip)]
            pub i32,
            pub i64,
            bool,
        )})?;
        let fields = Fields::<FieldReceiver>::try_from(&syn::Fields::Unnamed(fields))?;

        let collected = FieldsHelper::new(&fields).filtering(|_ix, f| !f.skip).collect();
        #[rustfmt::skip]
        let expected = quote!{(
            String,
            i64,
            bool
        )};

        assert_eq!(collected.to_string(), expected.to_string());

        let collected = FieldsHelper::new(&fields).include_visibility(true).collect();
        #[rustfmt::skip]
        let expected = quote!{(
            pub String,
            pub i32,
            pub i64,
            bool
        )};

        assert_eq!(collected.to_string(), expected.to_string());

        let collected = FieldsHelper::new(&fields)
            .filtering(|_ix, f| !f.skip)
            .include_all_default(true)
            .right_collector(FieldsCollector::ident)
            .collect();
        #[rustfmt::skip]
        let expected = quote!{(
            v_0,
            v_2,
            v_3,
            .. Default::default()
        )};

        assert_eq!(collected.to_string(), expected.to_string());

        let collected = FieldsHelper::new(&fields)
            .filtering(|_ix, f| !f.skip)
            .ignore_all_extra(true)
            .right_collector(FieldsCollector::ident)
            .collect();
        #[rustfmt::skip]
        let expected = quote!{(
            v_0,
            v_2,
            v_3,
            ..
        )};

        assert_eq!(collected.to_string(), expected.to_string());

        let collected = FieldsHelper::new(&fields)
            .with_attributes(|_ix, f| if f.skip { Some(quote!(#[skipped])) } else { None })
            .collect();
        #[rustfmt::skip]
        let expected = quote!{(
            String,
            #[skipped]
            i32,
            i64,
            bool
        )};

        assert_eq!(collected.to_string(), expected.to_string());

        Ok(())
    }
}
