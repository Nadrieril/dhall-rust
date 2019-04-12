// use std::error::Error;
// use std::io::{self, Read};
// use term_painter::ToStyle;

// const ERROR_STYLE: term_painter::Color = term_painter::Color::Red;
// const BOLD: term_painter::Attr = term_painter::Attr::Bold;

// fn print_error(message: &str, source: &str, start: usize, end: usize) {
//     let line_number = bytecount::count(source[..start].as_bytes(), b'\n');
//     let line_start = source[..start].rfind('\n').map(|i| i + 1).unwrap_or(0);
//     let line_end = source[end..].find('\n').unwrap_or(0) + end;
//     let context_prefix = &source[line_start..start];
//     let context_highlighted = &source[start..end];
//     let context_suffix = &source[end..line_end];

//     let line_number_str = line_number.to_string();
//     let line_number_width = line_number_str.len();

//     BOLD.with(|| {
//         ERROR_STYLE.with(|| {
//             print!("error: ");
//         });
//         println!("{}", message);
//     });
//     BOLD.with(|| {
//         print!("  -->");
//     });
//     println!(" (stdin):{}:0", line_number);
//     BOLD.with(|| {
//         println!("{:w$} |", "", w = line_number_width);
//         print!("{} |", line_number_str);
//     });
//     print!(" {}", context_prefix);
//     BOLD.with(|| {
//         ERROR_STYLE.with(|| {
//             print!("{}", context_highlighted);
//         });
//     });
//     println!("{}", context_suffix);
//     BOLD.with(|| {
//         print!("{:w$} |", "", w = line_number_width);
//         ERROR_STYLE.with(|| {
//             println!(
//                 " {:so$}{:^>ew$}",
//                 "",
//                 "",
//                 so = source[line_start..start].chars().count(),
//                 ew = ::std::cmp::max(1, source[start..end].chars().count())
//             );
//         });
//     });
// }

fn main() {
    // let mut buffer = String::new();
    // io::stdin().read_to_string(&mut buffer).unwrap();

    // TODO: public API is too restricted for this
    // let expr = match dhall::expr::Parsed::parse_str(&buffer) {
    //     Ok(expr) => expr,
    //     Err(e) => {
    //         print_error(&format!("Parse error {}", e), &buffer, 0, 0);
    //         return;
    //     }
    // };

    // let expr = expr.resolve().unwrap();

    // let expr = match expr.typecheck() {
    //     Ok(expr) => expr,
    //     Err(e) => {
    //         // TODO: implement pretty type error printing
    //         // let explain = ::std::env::args().any(|s| s == "--explain");
    //         // if !explain {
    //         //     term_painter::Color::BrightBlack.with(|| {
    //         //         println!("Use \"dhall --explain\" for detailed errors");
    //         //     });
    //         // }
    //         // ERROR_STYLE.with(|| print!("Error: "));
    //         // println!("{}", e.type_message.description());
    //         // if explain {
    //         //     println!("{}", e.type_message);
    //         // }
    //         // println!("{}", e.current);
    //         // // FIXME Print source position
    //         return;
    //     }
    // };

    // let expr = expr.normalize();

    // println!("{}", expr);
}
