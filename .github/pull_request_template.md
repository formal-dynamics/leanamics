## Summary

<!-- What does this pull request add or change? Name the roadmap ID(s), if any. -->

## Checklist

Every pull request that adds or changes a result keeps the documentation up to date. Tick what
you did; if an item does not apply, say why.

- [ ] The package `README.md` and blueprint (`blueprint/src/content.tex`, with `\lean{}` tags) are updated
- [ ] `FORMALIZATION_DIFFERENCES.md` lists every deviation from the source
- [ ] `RESULTS.md` has a row for each new or changed result
- [ ] `PROVENANCE.md` has an entry for each new or changed result
- [ ] The status in `ROADMAP.md` is updated
- [ ] The landing page `home_page/index.md` is updated, or an issue to update it is opened: #
- [ ] The build is `sorry`-free and the axiom audit passes (`python3 ../scripts/check_axioms.py` in the package)
