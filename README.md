# chrono-harness-judge-projects

执行选定项目的构建和测试并核验回执。

运行 `./check.sh` 验证独立组件。证明使用 Verus 0.2026.04.24.f8e1704，通过环境变量 `VERUS` 指定可执行文件。

[固定来源](https://github.com/ChronoAIProject/chrono-harness/tree/5f6892dfa2f73675a84e4ebdc3b06eb83b824d6e/crates/judge-projects)

项目判官从 FILEMAP 的公开命令读取受影响节点和已退役测试，生产 manifest 已移除 FILEMAP 的直接 Git 依赖。 运行时在宿主 PATH 中安装本仓 mise 清单固定的 chrono-judge-filemap。判官按已登记的超时、输出上限和环境调用 `impact-summary`。

`chrono-judge-projects check-pairs-v1` 从标准输入读取 JSON 对象。字段 `registry` 是固定提交的项目登记，`owners` 是本次变更影响的节点 ID 数组。命令先校验登记格式，再核对选中的项目和脚本的专属测试配对及语言。通过时退出 0，拒绝时向 stderr 写入原因并退出 2。该命令只读取传入的数据。

本仓从已合入 dev 的预发布标签构建 Linux x86_64 和 macOS arm64 的命令，正式标签指向 main。每个发行附两个二进制和 SHA256SUMS。各平台在上传前运行项目配对查询并验证错误输入的退出码。

工作流判官使用以下两个项目证据查询。两者从标准输入读取一个 JSON 对象，错误原因写入 stderr 并退出 2。

- `read-results-v1` 读取项目执行结果，输出 `results` 和 `passed`。前者使用项目判官原生序列化后的字段和默认值，供检查工作流凭证摘要时使用。
- `check-collection-v1` 在当前候选检出根运行。输入含 `request`、`effective_inputs`、`plan` 和 `results`。验证历史收集时，另传 `retained` 对象，其中的 `request` 和 `artifacts` 来自生产者报告。核验成功后退出 0，标准输出为空。

项目执行方通过宿主安装的 `chrono-judge-routes` 校验执行计划、核对原生执行回执，并在收集时重放声明。宿主可在 tools 中显式选择 routes 程序，或在 judges 中登记执行路径及 SHA-256。其余宿主使用有效 PATH 中的安装。业务子进程、并发调度和输出原件由 projects 持有。projects 在原执行目录记录编译器依赖文件和库的身份，发布回执后按本仓生命周期回收原件。单元收集按贡献者的原坐标核对回执，在收集检出调用已安装的判官。

`execute-plan-v1` 从标准输入接收 CI 已准备的执行计划。在计划的 `root` 目录运行。JSON 包含 `plan` 和 `routes`。后者提供已安装的 routes 的绝对路径 `executable`、`sha256`、查询时限 `timeout_seconds` 和 `output_limit_bytes`。projects 先校验 routes 程序及计划，再执行已登记的操作并等待所有 worker，最后在 stdout 返回 `{results, diagnostic_error}`。每个操作的退出码和原始输出保存在 results 的回执中。取得完整结果时命令退出 0，调用方从操作结果判断业务是否通过。输入、计划、执行器或结果传输异常时退出 2。

需要实时诊断的调用方可以传入 `diagnostics` 日志级别。每个 stderr 记录以 `chrono-trace-v1 ` 开头，随后是一条 tracing-tunnel 0.1 JSON 事件和换行。每个操作的父 span 在产生事件的 worker 中确定。诊断写入失败时，stdout 仍会返回执行结果和 `diagnostic_error`。
