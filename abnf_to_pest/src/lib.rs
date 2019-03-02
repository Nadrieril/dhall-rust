use std::collections::HashMap;
use itertools::Itertools;

pub struct PestRuleSettings {
    pub visible: bool,
    pub replace: Option<String>,
}

impl Default for PestRuleSettings {
    fn default() -> Self {
        PestRuleSettings { visible: true, replace: None }
    }
}

pub fn abnf_to_pest(data: &Vec<u8>, rule_settings: &HashMap<String, PestRuleSettings>) -> std::io::Result<String> {
    use abnf::abnf::*;
    use pretty::{Doc, BoxDoc};
    fn format_rule(x: Rule, rule_settings: &HashMap<String, PestRuleSettings>) -> Doc<BoxDoc<()>> {
        let rulename = format_rulename(x.name);
        let default = Default::default();
        let setting = rule_settings.get(&rulename).unwrap_or(&default);
        let visible = if setting.visible { "" } else { "_" };
        let contents = match setting.replace {
            None => format_alternation(x.elements),
            Some(ref x) => Doc::text(x.clone()),
        };
        Doc::nil()
            .append(Doc::text(rulename))
            .append(Doc::text(" = "))
            .append(Doc::text(visible))
            .append(Doc::text("{"))
            .append(Doc::space().append(contents).nest(2))
            .append(Doc::space())
            .append(Doc::text("}"))
            .group()
    }
    fn format_rulename(x: String) -> String {
        let x = x.replace("-", "_");
        if x == "if" || x == "else" || x == "as" || x == "let" || x == "in" || x == "fn" {
            x + "_"
        } else {
            x
        }
    }
    fn format_alternation(x: Alternation) -> Doc<'static, BoxDoc<'static, ()>> {
        Doc::intersperse(
            x.concatenations.into_iter().map(|x| format_concatenation(x).nest(2).group()),
            Doc::space().append(Doc::text("| "))
        )
    }
    fn format_concatenation(x: Concatenation) -> Doc<'static, BoxDoc<'static, ()>> {
        Doc::intersperse(
            x.repetitions.into_iter().map(format_repetition),
            Doc::space().append(Doc::text("~ "))
        )
    }
    fn format_repetition(x: Repetition) -> Doc<'static, BoxDoc<'static, ()>> {
        format_element(x.element)
            .append(x.repeat.map(format_repeat).map(Doc::text).unwrap_or(Doc::nil()))
    }
    fn format_repeat(x: Repeat) -> String {
        match (x.min.unwrap_or(0), x.max) {
            (0, None) => "*".into(),
            (1, None) => "+".into(),
            (0, Some(1)) => "?".into(),
            (min, None) => format!("{{{},}}", min),
            (min, Some(max)) if min == max => format!("{{{}}}", min),
            (min, Some(max)) => format!("{{{},{}}}", min, max),
        }
    }
    fn format_element(x: Element) -> Doc<'static, BoxDoc<'static, ()>> {
        use abnf::abnf::Element::*;
        match x {
            Rulename(s) => Doc::text(format_rulename(s)),
            Group(g) =>
                Doc::text("(")
                    .append(format_alternation(g.alternation).nest(4).group())
                    .append(Doc::text(")")),
            Option(o) =>
                Doc::text("(")
                    .append(format_alternation(o.alternation).nest(4).group())
                    .append(Doc::text(")?")),
            CharVal(s) => Doc::text(format!("^\"{}\"", s.replace("\"", "\\\"").replace("\\", "\\\\"))),
            NumVal(r) => Doc::text(format_range(r)),
            ProseVal(_) => unimplemented!(),
        }
    }
    fn format_range(x: Range) -> String {
        use abnf::abnf::Range::*;
        match x {
            Range(x, y) => format!("'{}'..'{}'", format_char(x), format_char(y)),
            OneOf(v) => format!("\"{}\"", v.into_iter().map(format_char).join("")),
        }
    }
    fn format_char(x: u64) -> String {
        if x <= (u8::max_value() as u64) {
            let x: u8 = x as u8;
            if x.is_ascii_graphic() {
                let x: char = x as char;
                if x != '"' && x != '\'' && x != '\\' {
                    return x.to_string();
                }
            }
        }
        format!("\\u{{{:02X}}}", x)
    }
    let make_err = |e| std::io::Error::new(std::io::ErrorKind::Other, format!("{}", e));

    let rules = rulelist_comp(&data).map_err(make_err)?.1;
    let formatted_rules = rules.into_iter().map(|x| format_rule(x, rule_settings));
    let doc: Doc<_> = Doc::intersperse(formatted_rules, Doc::newline());
    Ok(format!("{}", doc.pretty(80)))
}

