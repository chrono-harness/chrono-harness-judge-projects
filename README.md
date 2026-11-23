# chrono-harness-judge-projects

执行选定项目的构建和测试并核验回执。

运行 `./check.sh` 验证独立组件。证明使用 Verus 0.2026.04.24.f8e1704，通过环境变量 `VERUS` 指定可执行文件。

[固定来源](https://github.com/ChronoAIProject/chrono-harness/tree/5f6892dfa2f73675a84e4ebdc3b06eb83b824d6e/crates/judge-projects)

项目判官从 FILEMAP 的公开命令读取受影响节点和已退役测试，生产 manifest 已移除 FILEMAP 的直接 Git 依赖。 运行时在宿主 PATH 中安装本仓 mise 清单固定的 chrono-judge-filemap v0.1.0-alpha.1。判官按已登记的超时、输出上限和环境调用 `impact-summary`。

`chrono-judge-projects check-pairs-v1` 从标准输入读取 JSON 对象。字段 `registry` 是固定提交的项目登记，`owners` 是本次变更影响的节点 ID 数组。命令先校验登记格式，再核对选中的项目和脚本的专属测试配对及语言。通过时退出 0，拒绝时向 stderr 写入原因并退出 2。该命令只读取传入的数据。
