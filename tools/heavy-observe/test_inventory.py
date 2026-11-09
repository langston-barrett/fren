"""Check that the lifecycle controls are in the ordinary test inventory."""


def check(driver):
    jobs = driver.split('def jobs :', 1)[1].split('unsafe def runJob', 1)[0]
    handler = driver.split('  | "heavyProcess" :: mode => do', 1)[1].split('  | ["heavyBudget"] => do', 1)[0]
    assert '["heavyProcess", "tmpState"]' in jobs
    assert '"tmpState"' in handler.split('].contains part', 1)[0]


def controls(driver):
    check(driver)
    # These independent mutations reproduce the two omissions: neither may
    # pass the audit even though the Python part still exists.
    for original in ('["heavyProcess", "tmpState"]', '"automaticOwnership", "tmpState"'):
        assert original in driver
        mutated = driver.replace(original, original.replace('tmpState', 'missingPart'), 1)
        try:
            check(mutated)
        except AssertionError:
            continue
        raise AssertionError(f'inventory audit missed removal of {original}')
