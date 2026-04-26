## Flow Fixtures

`tests/flow/` contains the curated C corpus for the reconstructed milestone.

The fixtures are compiled with:

```sh
clang -emit-llvm -c -O0 -fno-inline -I.
```

Those flags matter:

- `-O0` keeps optimization disabled so the current fixtures preserve the
  original instruction structure;
- `-fno-inline` preserves helper calls so the adapter still sees them;
- `-I.` lets fixtures include `tests/local_assert.h`.

Current status:

- supported-shape fixtures are intended to stay within the adapter subset
  (integer arithmetic, `icmp`, `br`, integer `alloca` / `load` / `store` /
  `gep`, plain `call`, `ret`);
- unsupported fixtures are present on purpose so future smoke/debug runs can
  show explicit rejection for floating-point IR and other shapes still outside
  the active subset.

Use:

```sh
make -C tests smoke
```

to compile every fixture into `tests/out/` and run the CLI graph generator over
the resulting bitcode files.
