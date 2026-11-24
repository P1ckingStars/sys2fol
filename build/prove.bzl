"""sys_prove: sysprove run at build time, with the headers of its fol deps as the statements it may cite."""

load("@fol_zfc//build:fol.bzl", "FolInfo")

def _sys_prove_impl(ctx):
    headers = depset(transitive = [d[FolInfo].headers for d in ctx.attr.deps], order = "postorder")
    args = ctx.actions.args()
    for a in ctx.attr.arguments:
        a = ctx.expand_location(a, ctx.attr.srcs)
        for i, o in enumerate(ctx.outputs.outs):
            a = a.replace("{out%d}" % i, o.path)
        args.add(a)
    for h in headers.to_list():
        args.add("--lib", h)
    ctx.actions.run(
        outputs = ctx.outputs.outs,
        inputs = depset(ctx.files.srcs, transitive = [headers]),
        executable = ctx.executable._sysprove,
        arguments = [args],
        mnemonic = "SysProve",
        progress_message = "Writing proofs for %{label}",
    )
    return [DefaultInfo(files = depset(ctx.outputs.outs))]

sys_prove = rule(
    implementation = _sys_prove_impl,
    attrs = {
        "srcs": attr.label_list(allow_files = True),
        "deps": attr.label_list(providers = [FolInfo]),
        "outs": attr.output_list(mandatory = True),
        "arguments": attr.string_list(),
        "_sysprove": attr.label(default = "//src/tools:sysprove", executable = True, cfg = "exec"),
    },
)
