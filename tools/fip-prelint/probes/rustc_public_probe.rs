#![feature(rustc_private)]
extern crate rustc_driver;
extern crate rustc_hir;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_span;
#[macro_use]
extern crate rustc_public;

use rustc_middle::ty::TyCtxt;
use rustc_public::CrateDef;
use std::ops::ControlFlow;

fn crate_root_tool_attrs(tcx: TyCtxt<'_>, def_id: rustc_hir::def_id::DefId) -> Vec<String> {
    tcx.get_all_attrs(def_id)
        .iter()
        .filter_map(|a| match a {
            rustc_hir::Attribute::Unparsed(item) => {
                let p: Vec<String> = item.path.segments.iter().map(|s| s.as_str().to_string()).collect();
                Some(p.join("::"))
            }
            _ => None,
        })
        .collect()
}

fn analyze(tcx: TyCtxt<'_>) -> ControlFlow<(), ()> {
    let local = rustc_public::local_crate();
    println!("LOCAL crate root tool attrs: {:?}", crate_root_tool_attrs(tcx, rustc_hir::def_id::CRATE_DEF_ID.to_def_id()));
    for f in local.fn_defs() {
        let attrs: Vec<String> = f.all_tool_attrs().iter().map(|a| a.as_str().to_string()).collect();
        println!("LOCAL fn {} has_body={} attrs={attrs:?}", f.name(), f.has_body());
    }
    for c in rustc_public::external_crates() {
        if c.name != "dep" { continue; }
        let cnum = tcx.crates(()).iter().copied().find(|&n| tcx.crate_name(n).as_str() == "dep").unwrap();
        println!("DEP crate root tool attrs: {:?}", crate_root_tool_attrs(tcx, cnum.as_def_id()));
        for f in c.fn_defs() {
            let attrs: Vec<String> = f.all_tool_attrs().iter().map(|a| a.as_str().to_string()).collect();
            let blocks = f.body().map(|b| b.blocks.len());
            println!("DEP fn {} has_body={} blocks={blocks:?} attrs={attrs:?}", f.name(), f.has_body());
        }
    }
    ControlFlow::Continue(())
}

fn main() {
    let mut args: Vec<String> = std::env::args().collect();
    args.push("--sysroot".into());
    args.push(std::fs::read_to_string("/tmp/mirprobe/sysroot.txt").unwrap().trim().into());
    let r = run_driver!(&args, analyze, with_tcx);
    if let Err(e) = r { eprintln!("driver result: {e:?}"); }
}
