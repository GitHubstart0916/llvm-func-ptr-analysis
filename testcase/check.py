def analysis(a: str):
    a = "".join(a.strip().split())
    if a.endswith(')'):
        pos = a.find("(")
        a = a[:pos].strip()

    a = a.lstrip("/").strip()
    base = a.split(":")
    if len(base) != 2:
        print("para error")
        exit(1)
    # print(base)
    line_num = int(base[0])
    funcs = base[1].split(",")
    funcs.sort()
    return line_num, funcs


def init_map(suffix: str = ".c"):
    func_map = {}
    for i in range(20):
        file_name = "test" + str(i).zfill(2)
        func_map[file_name] = {}
        file = open(file_name + suffix)
        while True:
            line = file.readline()
            if not line:
                break
            if suffix == ".c" and line.startswith("/") and line.lstrip("/").lstrip()[0].isnumeric() or suffix == ".out":
                line_num, funcs = analysis(line)
                func_map[file_name][line_num] = funcs
    return func_map


def check_answer():
    ans_map = init_map(suffix=".c")
    out_map = init_map(suffix=".out")
    log = {}
    for key in out_map.keys():
        ans = ans_map[key]
        out = out_map[key]
        log_line = ""
        if len(ans) != len(out):
            log_line += "file_name: {} error, ans has {} lines but output has {} lines".format(key, len(ans), len(out))
            continue
        for line_num in out:
            if line_num not in ans.keys():
                log_line += "file_name:{} error, output has line {}, but ans not has".format(key, line_num)
            if ans[line_num] != out[line_num]:
                log_line += "file_name: {}, line_num: {} error, ans is {} but output is {}".format(key, line_num,
                                                                                                   " ".join(
                                                                                                       ans[line_num]),
                                                                                                   " ".join(
                                                                                                       out[line_num]))
        if log_line != "":
            log[key] = ("Wrong Answer", log_line)
        else:
            log[key] = ("Accept", "no error log, passed")
    return log


if __name__ == '__main__':
    log = check_answer()
    for key in log.keys():
        print("{}: {}, {}".format(key, log[key][0], log[key][1]))
