#![feature(rustc_private)]
extern crate rustc_driver;
extern crate rustc_hir;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_span;

use rustc_hir::def::{DefKind, Res};
use rustc_middle::ty::TyCtxt;

struct Probe {
    dep: String,
    func: String,
}

impl rustc_driver::Callbacks for Probe {
    fn after_analysis(&mut self, _c: &rustc_interface::interface::Compiler, tcx: TyCtxt<'_>) -> rustc_driver::Compilation {
        let mut found = false;
        for &cnum in tcx.crates(()) {
            if tcx.crate_name(cnum).as_str() != self.dep {
                continue;
            }
            for child in tcx.module_children(cnum.as_def_id()) {
                if let Res::Def(DefKind::Fn, def_id) = child.res
                    && child.ident.as_str() == self.func
                {
                    found = true;
                    let avail = tcx.is_mir_available(def_id);
                    print!("PROBE {}::{} is_mir_available={avail}", self.dep, self.func);
                    if avail {
                        let body = tcx.optimized_mir(def_id);
                        print!(" optimized_mir: {} basic blocks, {} locals", body.basic_blocks.len(), body.local_decls.len());
                    }
                    println!();
                }
            }
        }
        if !found {
            println!("PROBE {}::{} not found", self.dep, self.func);
        }
        rustc_driver::Compilation::Stop
    }
}

fn main() {
    let mut args: Vec<String> = std::env::args().collect();
    let dep = std::env::var("PROBE_DEP").expect("PROBE_DEP");
    let func = std::env::var("PROBE_FN").expect("PROBE_FN");
    args.push("--sysroot".into());
    args.push(std::fs::read_to_string("/tmp/mirprobe/sysroot.txt").unwrap().trim().into());
    rustc_driver::run_compiler(&args, &mut Probe { dep, func });
}
