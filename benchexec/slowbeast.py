# This file is part of BenchExec, a framework for reliable benchmarking:
# https://github.com/sosy-lab/benchexec
#
# SPDX-FileCopyrightText: 2007-2020 Dirk Beyer <https://www.sosy-lab.org>
#
# SPDX-License-Identifier: Apache-2.0

import benchexec.tools.template
import benchexec.result as result
import benchexec.util as util

class Tool(benchexec.tools.template.BaseTool):
    """
    This tool is an imaginary tool that returns always UNSAFE.
    To use it you need a normal benchmark-xml-file
    with the tool and tasks, however options are ignored.
    """

    def executable(self):
        return util.find_executable("sb")

    def name(self):
        return "slowbeast"

    def cmdline(self, executable, options, tasks, propertyfile, rlimits):
        return [executable] + options + tasks

    def determine_result(self, returncode, returnsignal, output, isTimeout):
        if output is None:
            return "{0}(no output)".format(result.RESULT_ERROR)

        noerrsline = False # the last line
        noerrs = False
        nokilledpaths = False
        hitassert = False
        for line in output:
            line = line.strip()
            if line.startswith("Found errors:"):
                noerrsline = True
                if line == "Found errors: 0":
                    noerrs = True
            elif 'assert False:bool' in line:
                hitassert = True
            elif line == "Killed paths: 0":
                nokilledpaths = True

        if not noerrsline:
            res = result.RESULT_ERROR
        elif noerrs and nokilledpaths:
            res = result.RESULT_TRUE_PROP
        elif not noerrs and hitassert:
            res = result.RESULT_FALSE_REACH
        else:
            res = result.RESULT_UNKNOWN

        if isTimeout:
            return res
        elif returnsignal != 0:
            return "KILLED (signal {0}, {1})".format(
                returnsignal, res
            )
        elif returncode != 0:
            return "{0}(returned {1}, {2})".format(
                result.RESULT_ERROR, returncode, res
            )
        else:
            return res

