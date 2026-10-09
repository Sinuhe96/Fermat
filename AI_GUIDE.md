# AI_GUIDE.md (bản khung v0.3)

Bạn là AI agent chạy bên trong **omp** (trợ lý AI chạy trong cửa sổ lệnh,
cài bằng `irm https://omp.sh/install.ps1 | iex`). Bạn có thể tự mở file,
chạy lệnh shell, đọc kết quả. Người dùng là người chỉ biết toán, đã đọc
`START_HERE.md`. Họ mở thư mục repo này trong omp rồi bảo bạn đọc file này.

Model đang chạy bạn (ví dụ `xiaomi/mimo-v2.6-flash` hoặc
`deepseek/deepseek-v4.1-flash` qua OpenRouter, hay model từ gói Google AI)
đủ cho toàn bộ việc dưới đây. Nếu người dùng hỏi model nào tốt: hai model
kia là lựa chọn rẻ đã kiểm chứng. Tránh model trả tiền có điều khoản dùng
dữ liệu người dùng để huấn luyện lại, trừ khi họ tự chọn.

## 1. Vai trò của bạn

- Bạn **tự làm mọi thứ làm được bằng công cụ của mình**: đọc file nội bộ,
  kiểm tra môi trường, chạy lệnh, đọc log. Chỉ hỏi người dùng khi không
  có công cụ nào trả lời được (ví dụ: máy bao nhiêu RAM khi bạn không đọc
  được, file PDF của họ ở đâu, họ muốn việc nào).
- Báo cho người dùng bằng **tiếng Việt**, ngắn gọn: bạn đang làm gì,
  xong thì kết quả gì, hỏng thì cần gì ở họ.
- Trước **mọi tác vụ chạy lâu** (tải GB dữ liệu, biên dịch Lean, quét tính
  toán lớn), báo trước ba điều: **làm gì, tại sao, mất khoảng bao lâu**
  (ước thô: vài phút / chục phút / hơn một giờ). Chờ họ đồng ý mới chạy.
- Không bắt họ gõ lệnh. Lệnh nào chạy được bằng công cụ của bạn thì bạn chạy.

## 2. Dựng máy cho người dùng (bạn tự làm, theo thứ tự)

Người dùng chạy PowerShell trên Windows. Container `lean` bên trong là
Linux. Lệnh shell chạy qua công cụ của bạn.

Người dùng có thể gọi bạn khi máy còn trắng (chưa có Docker, chưa có
repo). Bạn lo toàn bộ, theo thứ tự dưới đây. Người dùng chỉ làm đúng hai
việc: mở PowerShell (khung có dòng `PS`, không phải Command Prompt) và
đồng ý trước mỗi bước cài thêm / bước chạy lâu.

**Bước 0 — Lấy repo về máy.**
Nếu thư mục repo chưa tồn tại, clone vào `Documents\Fermat`:
```powershell
git clone https://github.com/Sinuhe96/Fermat.git Documents\Fermat
```
Nếu `git` thiếu: cài Git trước (báo người dùng một câu), rồi clone.
Lịch làm việc hằng ngày chạy từ trong thư mục này (`cd Documents\Fermat`
rồi mới `omp`) — nhưng lúc dựng máy thì bạn chạy ở đâu cũng được, miễn
là đường dẫn rõ ràng.

**Bước 1 — Docker Desktop và WSL.**
- `docker info` mà chạy: Docker đã sống, sang bước 2.
- Chưa có Docker: cài Docker Desktop cho Windows (báo trước: cài phần
  mềm mới, cần họ đồng ý). Sau khi cài, mở Docker Desktop, chờ hết quay.
- Docker có mà không kết nối được, hoặc báo lỗi WSL: kiểm tra WSL
  (`wsl -l -v`). Bật / sửa WSL theo thông báo lỗi, từng bước một.
  Kinh nghiệm xương máu: `winget` đòi **WindowsAppRuntime 1.8** mới chạy
  được — máy cài từ ISO sạch của Microsoft có thể thiếu, lỗi `winget`
  lúc đó không phải do mạng. Cài WindowsAppRuntime trước rồi mới dùng
  `winget`.
- Không giới hạn công cụ sửa Windows, nhưng **muốn cài thêm bất cứ phần
  mềm nào cũng phải giải thích và hỏi trước**: cài gì, tại sao, mất bao
  lâu. Không tự ý cài trong im lặng.

**Bước 2 — Image và khởi động.**
Trong thư mục repo:
```powershell
docker compose pull lean
docker compose up -d lean
```
Báo trước: tải khoảng 600 MB nếu chưa có.

**Bước 3 — RAM và `.wslconfig` (chỉ khi container thiếu bộ nhớ).**
Nếu `check_env.sh` ở bước 4 báo hết bộ nhớ, hoặc biên dịch chết không
rõ lý do, mới kiểm tra RAM máy host. Chuẩn đã kiểm chứng trên máy 16 GB:
file `.wslconfig.example` trong repo (`memory=13GB`, `swap=6GB`,
`autoMemoryReclaim=gradual`). Người dùng tự copy thành `.wslconfig`
trong thư mục người dùng của họ (file nằm ngoài repo nên bạn không tự
ghi được thì hướng dẫn họ từng thao tác), rồi `wsl --shutdown` và mở
Docker Desktop lại. Nếu bạn ghi được file thẳng vào thư mục người dùng
thì tự làm, báo họ một câu là xong.
Máy 12 GB: dùng `memory=10GB`, `swap=8GB`, và từ đây bạn làm thưa hơn
(mỗi lần một kiểm tra nặng), báo trước là chạy chậm hơn.
Xong thì kiểm tra lại từ bước 2.

**Bước 4 — Đọc trạng thái repo.**
Đọc `HANDOFF.md` (một dòng trạng thái + bước tiếp theo), `README.md`
(lệnh vận hành), rồi `AGENTS.md` (quy trình, bắt buộc toàn bộ).
Ghi nhớ bước tiếp theo đang dở, nhưng đừng làm ngay — xong kiểm tra
môi trường đã.

**Bước 5 — Kiểm tra nhanh.**
```powershell
docker compose exec -T lean sh /workspace/proof/check_env.sh
```
- `SMOKE PASS (fast)`: môi trường xanh. Sang mục 3.
- Thiếu `Mathlib.olean`, thiếu dự án Lake, hoặc `SMOKE FAIL` ở mục
  `runtime layout`: cần khởi tạo lần đầu. **Báo trước**: tải khoảng
  11 GB, có thể hơn một giờ tùy mạng. Chờ họ đồng ý, rồi chạy:
  ```powershell
  docker compose exec -T lean sh /workspace/proof/init_work.sh
  ```
  Script tự bỏ qua bước đã xong. Kết thúc phải thấy `init_work.sh: DONE`.
- Lỗi khác: dừng. Xin nguyên văn thông báo từ họ nếu lỗi nằm ngoài
  công cụ của bạn, không đoán.

**Kiểm tra đầy đủ (khi cần).**
Chỉ sau khi đổi image, đổi toolchain, hoặc sửa cache. Báo trước:
biên dịch `import Mathlib` mất vài phút.
```powershell
docker compose exec -T lean sh /workspace/proof/check_env.sh --full
```

## 3. Hỏi người dùng muốn làm gì

Chỉ sau khi môi trường xanh. Có đúng hai việc, cho họ chọn một:

1. **Kiểm tra một chứng minh có sẵn** (họ đưa file PDF chứng minh).
   Họ chỉ cần cho bạn biết file ở đâu. Phần còn lại bạn tự làm.
2. **Tìm chứng minh hoặc phản ví dụ cho một giả thuyết.**
   Họ cho bạn phát biểu đầy đủ: giả thiết là gì, kết luận là gì.

Đọc thầm tài liệu nền trước khi động tay:
- Việc 1: `AGENTS.md` (toàn bộ), `pipeline/PIPELINE.md`, `HANDOFF.md`.
- Việc 2: `HANDOFF_CONJECTURE.md`, `NEW_CONJECTURE.md`, `Phase2_Feedback.md`.

## 4. Track 1 — Kiểm tra chứng minh có sẵn

- Nguyên tắc cao nhất: **chép đúng từng bước của tác giả, để máy kiểm tra**.
- Bước tác giả sai mà máy báo lỗi: dừng tại đó, ghi lại thành câu hỏi
  cho tác giả (trích đúng chỗ sai, thông báo lỗi nguyên văn, ví dụ nhỏ
  nhất nếu có). Báo người dùng bằng tiếng Việt: sai ở đâu, nghĩa là gì,
  cần gì tiếp (thường là câu trả lời của tác giả). Không làm tiếp phần sau.
- Làm từng bước nhỏ, mỗi bước kiểm tra bằng máy ngay. Mỗi lần biên dịch
  là một tác vụ chạy lâu (vài phút): **báo trước rồi mới chạy**, đừng
  dồn nhiều bước vào một lần kiểm tra.
- Nguồn Lean sửa trong `pipeline/03-lean/`, kiểm tra bằng
  `compile_lean.sh` (script tự copy vào volume Linux rồi biên dịch).
  Không sửa file trong `/workspace/work`, không chạy `lake`/`lean` ở
  thư mục Windows nào.
- Chi tiết quy trình (chia nhỏ, trích dẫn, đối chiếu, phân loại kết quả)
  nằm trong `AGENTS.md`. Bạn tuân theo, người dùng không cần đọc.
- Báo tiến độ thưa, theo mốc (xong một bước, xong một nhóm bước), không
  báo từng lệnh.

## 5. Track 2 — Tìm chứng minh hoặc phản ví dụ

- Thứ tự: **thử tính toán trước, chứng minh sau.** Dùng Python / SymPy
  trong container để thử hàng loạt trường hợp, tìm phản ví dụ. Mỗi đợt
  quét lớn là tác vụ chạy lâu: báo trước phạm vi + thời gian ước tính.
- Có phản ví dụ là xong việc: ghi lại nó (giá trị cụ thể, kiểm chứng
  lại được), báo người dùng.
- Không có phản ví dụ chỉ là tín hiệu tốt, **không phải chứng minh**.
  Nói rõ điều này, không để họ hiểu lầm.
- Chỉ formalize bằng Lean phần nào đã chắc (hằng đẳng thức, bổ đề rời
  rạc). Mỗi khẳng định Lean phải qua máy kiểm tra như track 1.
- Không bao giờ tuyên bố "giả thuyết đúng/được chứng minh" khi mới chỉ
  có kết quả tính toán trên phạm vi hữu hạn.

## 6. Danh sách cấm (không bao giờ làm)

- `docker compose down -v` (xóa hàng GB dữ liệu, phải tải lại).
  Dừng bình thường chỉ dùng `docker compose down`.
- Tự build image (`docker compose build`) khi chưa được chủ repo yêu cầu.
- Chạy `lake`, `lean`, hoặc biên dịch trong `proof/`, `pipeline/`,
  `proof_verify/` hoặc bất kỳ thư mục Windows nào. Mọi việc Lean chỉ
  chạy trong `/workspace/work` (volume Linux), qua `compile_lean.sh`.
- Sửa file trực tiếp trong `/workspace/work`. Nguồn thật nằm trong repo.
- Chạy hai lần biên dịch nặng cùng lúc. Mỗi lần một cái.
- Đặt `sorry` (bỏ qua chứng minh) rồi báo là xong.
- Chạy tác vụ lâu mà không báo trước (làm gì, tại sao, bao lâu) và chưa
  được người dùng đồng ý.

## 7. Khi bí

Dừng lại. Tóm tắt cho người dùng bằng tiếng Việt: đã làm đến đâu, kết
quả máy báo gì (nguyên văn phần quan trọng), bạn nghi ngờ chỗ nào, và
cần gì tiếp theo (thông tin từ họ, hay câu trả lời của tác giả chứng
minh). Không bịa lệnh mới để thử đại.
