use darling::ast::Fields;
use proc_macro2::TokenStream;
use quote::{quote, ToTokens};

use crate::{FieldInfo, FieldsCollector, FieldsHelper};

/// Utility macro to implement [VariantInfo]
#[macro_export]
macro_rules! variant_info {
    ($v:path, $f:path) => {
        impl $crate::VariantInfo<$f> for $v {
            fn ident(&self) -> &syn::Ident {
                &self.ident
            }

            fn discriminant(&self) -> &Option<syn::Expr> {
                &self.discriminant
            }

            fn fields(&self) -> &darling::ast::Fields<$f> {
                &self.fields
            }
        }
    };
}

/// Trait to retrieve variants' properties
pub trait VariantInfo<F: FieldInfo> {
    /// Retrieves the identifier of the passed-in variant
    fn ident(&self) -> &syn::Ident;
    /// Retrieves the variant discriminant (if any). For a variant such as `Example = 2`, the `2`
    fn discriminant(&self) -> &Option<syn::Expr>;
    /// Retrieves the fields associated with the variant
    fn fields(&self) -> &Fields<F>;
    /// Retrieves the discriminant expr, if any (`= 3`)
    fn discriminant_expr(&self) -> TokenStream {
        self.discriminant()
            .as_ref()
            .map(|d| {
                let expr = d.to_token_stream();
                quote!(= #expr)
            })
            .unwrap_or_default()
    }
}

/// Utility struct to work with enum's variants
pub struct VariantsHelper<'v, V: VariantInfo<F>, F: FieldInfo> {
    variants: Vec<&'v V>,
    variant_filter: Option<Box<dyn Fn(&V) -> bool + 'v>>,
    variant_attributes: Option<Box<dyn Fn(&V) -> Option<TokenStream> + 'v>>,
    include_extra_variants: Vec<(TokenStream, Option<TokenStream>)>,
    ignore_all_extra_variants: Option<TokenStream>,
    include_wrapper: bool,
    left_collector: Option<Box<dyn Fn(&V, FieldsHelper<'_, F>) -> TokenStream + 'v>>,
    right_collector: Option<Box<dyn Fn(&V, FieldsHelper<'_, F>) -> TokenStream + 'v>>,
}

impl<'v, V: VariantInfo<F>, F: FieldInfo> VariantsHelper<'v, V, F> {
    /// Builds a new [VariantsHelper]
    pub fn new(variants: &'v [V]) -> Self {
        Self {
            variants: variants.iter().collect(),
            variant_filter: None,
            variant_attributes: None,
            include_extra_variants: Vec::new(),
            ignore_all_extra_variants: None,
            include_wrapper: true,
            left_collector: None,
            right_collector: None,
        }
    }

    /// Remove all variants `v` for which `predicate(&v)` returns `false`.
    /// This method operates in place, visiting each element exactly once in the
    /// original order, and preserves the order of the retained elements.
    pub fn filtering_variants<P>(mut self, predicate: P) -> Self
    where
        P: Fn(&V) -> bool + 'v,
    {
        self.variant_filter = Some(Box::new(predicate));
        self
    }

    /// Adds an arbitrary number of attributes to each variant.
    pub fn with_variant_attributes<P>(mut self, predicate: P) -> Self
    where
        P: Fn(&V) -> Option<TokenStream> + 'v,
    {
        self.variant_attributes = Some(Box::new(predicate));
        self
    }

    /// Include extra variants by including the given left and right sides (`#left` if right is [None] or `#left =>
    /// #right`) at the end.
    pub fn include_extra_variants(
        mut self,
        include_extra_variants: impl IntoIterator<Item = (impl ToTokens, Option<impl ToTokens>)>,
    ) -> Self {
        let mut include_extra_variants = include_extra_variants
            .into_iter()
            .map(|(l, r)| (l.to_token_stream(), r.map(|t| t.to_token_stream())))
            .collect::<Vec<_>>();
        self.include_extra_variants.append(&mut include_extra_variants);
        self
    }

    /// Wether to ignore all extra variants with the given right side `_ => #right`, if [Some].
    ///
    /// It should be used only when collecting a match.
    pub fn ignore_all_extra_variants(mut self, right_side: Option<TokenStream>) -> Self {
        self.ignore_all_extra_variants = right_side;
        self
    }

    /// Wether to include the wrapper (curly braces), defaults to `true`.
    pub fn include_wrapper(mut self, include_wrapper: bool) -> Self {
        self.include_wrapper = include_wrapper;
        self
    }

    /// Specifies the left collector.
    ///
    /// Defaults to `VariantsCollector::variant_definition`
    pub fn left_collector<C>(mut self, left_collector: C) -> Self
    where
        C: Fn(&V, FieldsHelper<'_, F>) -> TokenStream + 'v,
    {
        self.left_collector = Some(Box::new(left_collector));
        self
    }

    /// Specifies the right collector.
    ///
    /// Defaults to `VariantsCollector::empty`
    pub fn right_collector<C>(mut self, right_collector: C) -> Self
    where
        C: Fn(&V, FieldsHelper<'_, F>) -> TokenStream + 'v,
    {
        self.right_collector = Some(Box::new(right_collector));
        self
    }

    /// Collects the fields.
    ///
    /// # Examples
    /// If using the default collectors:
    /// ``` ignore
    /// {
    ///     Variant1,
    ///     Variant2 = 5,
    ///     Variant3 {
    ///         field_1: String,
    ///         field_2: i32,
    ///     },
    /// }
    /// ```
    ///
    /// If using `VariantsCollector::variant_fields_collector(quote!(SelfTy))` left collector and
    /// `VariantsCollector::variant_fields_collector(quote!(OtherTy)` right
    /// collector:
    /// ``` ignore
    /// {
    ///     SelfTy::Variant1 => OtherTy::Variant1,
    ///     SelfTy::Variant2 {
    ///         field_1: field_1,
    ///         field_2: field_2,
    ///     } => OtherTy::Variant2 {
    ///         field_1: field_1,
    ///         field_2: field_2,
    ///     },
    /// }
    /// ```
    pub fn collect(self) -> TokenStream {
        let left_collector = self
            .left_collector
            .unwrap_or_else(|| Box::new(VariantsCollector::empty));

        let mut variants = self
            .variants
            .into_iter()
            .filter(|&v| {
                if let Some(variant_filter_fn) = &self.variant_filter {
                    variant_filter_fn(v)
                } else {
                    true
                }
            })
            .map(|v| {
                let attrs = if let Some(attrs_fn) = &self.variant_attributes {
                    attrs_fn(v)
                } else {
                    None
                }
                .unwrap_or_default();

                let left = left_collector(v, FieldsHelper::new(v.fields()));
                let right = if let Some(right_collector) = &self.right_collector {
                    let right = right_collector(v, FieldsHelper::new(v.fields()));
                    quote!(=> #right)
                } else {
                    TokenStream::default()
                };

                quote!(
                    #attrs
                    #left #right
                )
            })
            .collect::<Vec<_>>();

        for (left, right) in self.include_extra_variants {
            let right = right.map(|r| quote!(=> #r)).unwrap_or_default();
            variants.push(quote!(#left #right));
        }

        if let Some(right) = self.ignore_all_extra_variants {
            variants.push(quote!(_ => #right));
        }

        if self.include_wrapper {
            quote!(
                {
                    #( #variants ),*
                }
            )
        } else {
            quote!( #( #variants ),* )
        }
    }
}

/// Utility struct with common collectors for [VariantsHelper]
pub struct VariantsCollector;
impl VariantsCollector {
    /// Empty collector
    pub fn empty<V, F>(_v: &V, _f: FieldsHelper<'_, F>) -> TokenStream
    where
        V: VariantInfo<F>,
        F: FieldInfo,
    {
        TokenStream::default()
    }

    /// Variant definition collector
    ///
    /// ## Examples
    /// ``` ignore
    /// {
    ///     Variant1,
    ///     Variant2 = 5,
    ///     Variant3 {
    ///         field_1: String,
    ///         field_2: i32,
    ///     },
    /// }
    /// ```
    pub fn variant_definition<V, F>(v: &V, fields: FieldsHelper<'_, F>) -> TokenStream
    where
        V: VariantInfo<F>,
        F: FieldInfo,
    {
        let ident = v.ident();
        let dis = v.discriminant_expr();
        let fields_expr = fields.collect();
        quote!(
            #ident #dis #fields_expr
        )
    }

    /// Collects the fields of a variant
    ///
    /// ## Examples
    /// An unit variant:
    /// ``` ignore
    /// Ty::Variant1
    /// ```
    /// A variant with unnamed fields:
    /// ``` ignore
    /// Ty::Variant2 (v_0, v_1)
    /// ```
    /// A variant with named fields:
    /// ``` ignore
    /// Ty::Variant3 {
    ///     field_1: field_1,
    ///     field_2: field_2,
    /// }
    /// ```
    pub fn variant_fields_collector<V, F>(ty: impl ToTokens) -> impl Fn(&V, FieldsHelper<'_, F>) -> TokenStream
    where
        V: VariantInfo<F>,
        F: FieldInfo,
    {
        move |v, fields| {
            let ident = v.ident();
            let right = fields.right_collector(FieldsCollector::ident).collect();
            quote!( #ty::#ident #right )
        }
    }
}

#[cfg(test)]
mod tests {
    #![allow(clippy::manual_unwrap_or_default)] // darling macro

    use darling::{FromField, FromVariant};
    use quote::quote;
    use syn::Result;

    use super::*;
    use crate::field_info;

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
        pub skip: bool,
    }
    field_info!(FieldReceiver);

    #[derive(FromVariant, Clone)]
    #[darling(attributes(tst))]
    struct VariantReceiver {
        /// The identifier of the passed-in variant
        ident: syn::Ident,
        /// For a variant such as `Example = 2`, the `2`
        discriminant: Option<syn::Expr>,
        /// The fields associated with the variant
        fields: Fields<FieldReceiver>,

        /// Whether to skip
        #[darling(default)]
        skip: bool,
    }
    variant_info!(VariantReceiver, FieldReceiver);

    #[test]
    fn test_variant_helper() -> Result<()> {
        let input: syn::DeriveInput = syn::parse2(quote! {
            pub enum MyEnum {
                Variant1,
                #[tst(skip)]
                Variant2,
                Variant3 (String, i64),
                Variant4 {
                    field_1: String,
                    #[tst(skip)]
                    field_2: i32,
                    field_3: bool,
                }
            }
        })?;
        let variants = darling::ast::Data::<VariantReceiver, FieldReceiver>::try_from(&input.data)?
            .take_enum()
            .unwrap();

        let collected = VariantsHelper::new(&variants)
            .filtering_variants(|v| !v.skip)
            .left_collector(|v, fields| {
                let ident = &v.ident;
                let dis = v.discriminant_expr();
                let fields_expr = fields.filtering(|_ix, f| !f.skip).collect();
                quote!(
                    #ident #dis #fields_expr
                )
            })
            .collect();
        #[rustfmt::skip]
        let expected = quote!({
            Variant1,
            Variant3 (String, i64),
            Variant4 {
                field_1: String,
                field_3: bool
            }
        });

        assert_eq!(collected.to_string(), expected.to_string());

        let collected = VariantsHelper::new(&variants)
            .with_variant_attributes(|v| if v.skip { Some(quote!(#[skipped])) } else { None })
            .left_collector(|v, fields| {
                let ident = &v.ident;
                let dis = v.discriminant_expr();
                let fields_expr = fields.filtering(|_ix, f| !f.skip).include_all_default(true).collect();
                quote!(
                    #ident #dis #fields_expr
                )
            })
            .collect();
        #[rustfmt::skip]
        let expected = quote!({
            Variant1,
            #[skipped]
            Variant2,
            Variant3 (String, i64, .. Default::default()),
            Variant4 {
                field_1: String,
                field_3: bool,
                .. Default::default()
            }
        });

        assert_eq!(collected.to_string(), expected.to_string());

        let collected = VariantsHelper::new(&variants)
            .filtering_variants(|v| !v.skip)
            .left_collector(|v, fields| {
                let ident = &v.ident;
                let dis = v.discriminant_expr();
                let fields_expr = fields
                    .with_attributes(|_ix, f| if f.skip { Some(quote!(#[skipped])) } else { None })
                    .ignore_all_extra(true)
                    .collect();
                quote!(
                    #ident #dis #fields_expr
                )
            })
            .collect();
        #[rustfmt::skip]
        let expected = quote!({
            Variant1,
            Variant3 (String, i64, ..),
            Variant4 {
                field_1: String,
                #[skipped]
                field_2: i32,
                field_3: bool,
                ..
            }
        });

        assert_eq!(collected.to_string(), expected.to_string());

        let collected = VariantsHelper::new(&variants)
            .filtering_variants(|v| !v.skip)
            .left_collector(|v, fields| {
                let ident = &v.ident;
                let fields_expr = fields
                    .filtering(|_ix, f| !f.skip)
                    .right_collector(FieldsCollector::ident)
                    .collect();
                quote!( MyEnum1::#ident #fields_expr )
            })
            .right_collector(|v, fields| {
                let ident = &v.ident;
                let fields_expr = fields
                    .filtering(|_ix, f| !f.skip)
                    .right_collector(FieldsCollector::ident)
                    .collect();
                quote!( MyEnum2::#ident #fields_expr )
            })
            .collect();
        #[rustfmt::skip]
        let expected = quote!({
            MyEnum1::Variant1 => MyEnum2::Variant1,
            MyEnum1::Variant3 (v_0, v_1) => MyEnum2::Variant3 (v_0, v_1),
            MyEnum1::Variant4 {
                field_1: field_1,
                field_3: field_3
            } => MyEnum2::Variant4 {
                field_1: field_1,
                field_3: field_3
            }
        });

        assert_eq!(collected.to_string(), expected.to_string());

        let collected = VariantsHelper::new(&variants)
            .left_collector(|v, fields| {
                let ident = &v.ident;
                let fields_expr = fields
                    .ignore_all_extra(true)
                    .right_collector(FieldsCollector::ident)
                    .collect();
                quote!( MyEnum1::#ident #fields_expr )
            })
            .right_collector(|v, fields| {
                let ident = &v.ident;
                let fields_expr = fields
                    .include_all_default(true)
                    .right_collector(FieldsCollector::ident)
                    .collect();
                quote!( MyEnum2::#ident #fields_expr )
            })
            .collect();
        #[rustfmt::skip]
        let expected = quote!({
            MyEnum1::Variant1 => MyEnum2::Variant1,
            MyEnum1::Variant2 => MyEnum2::Variant2,
            MyEnum1::Variant3 (v_0, v_1, ..) => MyEnum2::Variant3 (v_0, v_1, ..Default::default()),
            MyEnum1::Variant4 {
                field_1: field_1,
                field_2: field_2,
                field_3: field_3,
                ..
            } => MyEnum2::Variant4 {
                field_1: field_1,
                field_2: field_2,
                field_3: field_3,
                ..Default::default()
            }
        });

        assert_eq!(collected.to_string(), expected.to_string());

        Ok(())
    }
}
