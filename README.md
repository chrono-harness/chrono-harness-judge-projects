# chrono-harness-judge-projects

执行选定项目的构建和测试并核验回执。

运行 `./check.sh` 验证独立组件。证明使用 Verus 0.2026.04.24.f8e1704，通过环境变量 `VERUS` 指定可执行文件。

[固定来源](https://github.com/ChronoAIProject/chrono-harness/tree/5f6892dfa2f73675a84e4ebdc3b06eb83b824d6e/crates/judge-projects)

项目判官从 FILEMAP 的公开命令读取受影响节点和已退役测试，生产 manifest 已移除 FILEMAP 的直接 Git 依赖。 运行时在宿主 PATH 中安装本仓 mise 清单固定的 chrono-judge-filemap。判官按已登记的超时、输出上限和环境调用 `impact-summary`。

`chrono-judge-projects check-pairs-v1` 从标准输入读取 JSON 对象。字段 `registry` 是固定提交的项目登记，`owners` 是本次变更影响的节点 ID 数组。命令先校验登记格式，再核对选中的项目和脚本的专属测试配对及语言。通过时退出 0，拒绝时向 stderr 写入原因并退出 2。该命令只读取传入的数据。

本仓从已合入 dev 的预发布标签构建 Linux x86_64 和 macOS arm64 的命令，正式标签指向 main。每个发行附两个二进制和 SHA256SUMS。各平台在上传前运行项目配对查询并验证错误输入的退出码。

工作流判官使用以下两个项目证据查询。两者从标准输入读取一个 JSON 对象，错误原因写入 stderr 并退出 2。

- `read-results-v1` 读取项目执行结果，输出 `results` 和 `passed`。前者使用项目判官原生序列化后的字段和默认值，供检查工作流凭证摘要时使用。每个选中的测试都须有完整的 `passed` 结果。未记录或失败时 `passed` 返回 false。
- `check-collection-v1` 在当前候选检出根运行。输入含 `request`、`effective_inputs`、`plan` 和 `results`。验证历史收集时，另传 `retained` 对象，其中的 `request` 和 `artifacts` 来自生产者报告。核验成功后退出 0，标准输出为空。

项目执行方通过宿主安装的 `chrono-judge-routes` 校验执行计划、核对原生执行回执，并在收集时重放声明。宿主可在 tools 中显式选择 routes 程序，或在 judges 中登记执行路径及 SHA-256。其余宿主使用有效 PATH 中的安装。业务子进程、并发调度和输出原件由 projects 持有。projects 在原执行目录记录编译器依赖文件和库的身份，发布回执后按本仓生命周期回收原件。单元收集按贡献者的原坐标核对回执，在收集检出调用已安装的判官。

本仓的生产和测试 Cargo 项目独立构建。运行时使用本仓 mise 配置固定的 runner 和判官发行文件。

`execute-plan-v1` 从标准输入接收 CI 已准备的执行计划。在计划的 `root` 目录运行。JSON 包含 `plan` 和 `routes`。后者提供已安装的 routes 的绝对路径 `executable`、`sha256`、查询时限 `timeout_seconds` 和 `output_limit_bytes`。projects 先校验 routes 程序及计划，再执行已登记的操作并等待所有 worker，最后在 stdout 返回 `{results, diagnostic_error}`。每个操作结束后，projects 把已验计划中的该项方法、工具、环境及实际回执交给 routes 的 `check-operation-receipt-v1`。每个操作的退出码和原始输出保存在 results 的回执中。操作失败时，`error` 同时报告退出码及操作自己给出的 `E_VERUS_COVERAGE` 原因。执行者先读完整 stderr，再读完整 stdout，采用首条正文为 1 至 1024 字节、含可见文本且无控制字符的独占诊断行。缺少合格诊断时仅报告退出码。Git、命令和原件由宿主安装的 runner 执行。收集器通过 `judge-evidence-v1` 核对报告，执行者通过 `retained-artifacts-v1` 持有目录和进程原件，调用 `compiler-output-v1` 读取已完成的编译输出。独立调用通过 `selected-host-config-v1` 读取当前平台配置中的 runner 路径。没有宿主配置时从 PATH 解析 `chrono-harness`。取得完整结果时命令退出 0，调用方从操作结果判断业务是否通过。输入、计划、执行器或结果传输异常时退出 2。

需要实时诊断的调用方可以传入 `diagnostics` 日志级别。每个 stderr 记录以 `chrono-trace-v1 ` 开头，随后是一条 tracing-tunnel 0.1 JSON 事件和换行。每个操作的父 span 在产生事件的 worker 中确定。诊断写入失败时，stdout 仍会返回执行结果和 `diagnostic_error`。

执行普通和单元计划前，projects 用安装的 routes 的 `dispatch-plan-v1` 校验计划，读取并发上限和完整操作下标次序。启动进程前先核对计划身份和下标覆盖。正在运行的操作继续占用原计划声明的资源与输出路径，完成后再检查下一批就绪操作。

项目登记通过已安装的 `chrono-judge-registration` 解释。执行和收集从固定端点取得登记，按宿主选择的程序调用 `project-views-v1`。执行结束后重查现场输入，收集时从原产物和保留视图核对有效输入。`check-pairs-v1` 从当前宿主的 `.chrono-harness/config.json` 选定登记程序，独立调用时可从 PATH 提供。配对、语言和真实执行证据仍由 projects 判定。安装本仓固定的 registration 发行即可运行这些入口。

## 开发机检查原件

本仓在每次操作目录生成 Verus 库与 dep-info，项目判官核查登记证据后释放。成功的本地最后一份报告按 24 小时窗口保留，到期维护会等待真实读者退出。需要长期保存的原件在窗口内转存并从检出外读回。维护入口与本仓选择见[开发机检查原件](.chrono-harness/USAGE.md#开发机检查原件)。

GitHub Actions 的单元原件保留 1 天。汇总归档随 GitHub 仓库设置滚动；采用时仓库配置为 90 天。

### 已登记的断言 helper

专属测试若把断言交给已有的独立操作，可在 projects v2 的测试行登记 `assertion_helpers`。例如 `{"test:word_count_test":["words.check-result"]}` 把该操作的断言职责归给指定测试。使用支持该字段的 registration 和 projects 判官，并在该测试的 FILEMAP 执行计划登记同一操作。

full 运行从已核对的操作方法取得所有者及其语言，从原进程取得实际参数和回执身份。语言冲突返回 `E_TEST_LANGUAGE`。Shell 生产单元可使用 Python 测试。单元原件在汇总时再次核对定位到该测试和操作的证据。未登记断言职责的后代，其语言仍未知。

执行器可读取 routes v2 计划中的完整 u64 超时。超过 9007199254740991 的超时在计划和操作回执中以十进制字符串传输，安全范围内继续使用 JSON 整数。原生运行和进程原件发布按实际的数值上限执行；重放原件时，使用绑定的计划身份验证回执。
