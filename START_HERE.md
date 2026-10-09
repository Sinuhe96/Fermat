# Bắt đầu từ đây

Repo này dùng máy tính để kiểm tra chứng minh toán học. Bạn không cần biết lập trình. Bạn làm việc với một AI, AI lo toàn bộ phần máy móc — kể cả cài đặt.

## Repo này làm được hai việc

**1. Kiểm tra một chứng minh có sẵn.**
Ví dụ: file `PROOF_of_FERMAT.pdf` trong repo là một chứng minh Định lý Fermat lớn (33 trang). Bạn đưa chứng minh, máy tính (Lean) kiểm tra từng bước suy luận đúng hay sai.

**2. Tìm chứng minh hoặc phản ví dụ cho một giả thuyết.**
Ví dụ: file `NEW_CONJECTURE.md` trong repo nêu một mệnh đề về giá trị n-adic của đa thức. Máy tính thử hàng nghìn trường hợp để tìm phản ví dụ, rồi ghi lại lập luận.

Bạn chỉ cần nói cho AI biết mình muốn việc nào.

## Máy của bạn cần gì

- Máy Windows 10 hoặc 11, 64-bit.
- RAM nên có **16 GB**. Máy 12 GB vẫn chạy được nhưng chậm hơn.
- Ổ cứng còn trống khoảng **15 GB**.
- Không cần cài Python hay Lean. AI lo hết.

## Bắt đầu (ba bước)

Mở **PowerShell** (không phải Command Prompt — khung có dòng chữ `PS`). Gõ từng lệnh dưới đây.

### 1. Cài omp (trợ lý AI)

```powershell
irm https://omp.sh/install.ps1 | iex
```

Lệnh này cài một file duy nhất.

### 2. Cho omp một mô hình AI (để AI có não)

Lần đầu bạn gõ `omp`, nó tự hiện menu hỏi: đăng ký gói (subscription) hay nhập API key — cứ làm theo menu, không cần nhớ lệnh nào.

- **Bạn đã trả tiền gói Google AI.** Chọn Google trong menu, làm theo hướng dẫn trên màn hình.
- **Bạn mua credit OpenRouter.** Tạo tài khoản tại `openrouter.ai`, nạp một ít credit, tạo một API key, rồi dán vào khi menu hỏi.

Muốn đổi tài khoản về sau mới cần lệnh: gõ `/login` (chọn Google) hoặc `/login openrouter` (dán key mới).

Khi omp hỏi dùng mô hình nào, chọn một trong hai (rẻ, đủ khỏe):

- `xiaomi/mimo-v2.6-flash`
- `deepseek/deepseek-v4.1-flash`

Kẹt ở bước này? Mở omp lên và bảo AI: "giúp tôi đăng nhập". Nó tự dẫn bạn đi tiếp.

### 3. Bảo AI dựng mọi thứ còn lại

Gõ `omp` để mở trợ lý (làm trong thư mục người dùng của bạn là được, không cần vào đâu xa), rồi bảo:

> Lấy repo Fermat về máy giúp tôi: `git clone https://github.com/Sinuhe96/Fermat.git` vào `Documents\Fermat` trong thư mục người dùng của tôi. Rồi đọc file `AI_GUIDE.md` trong đó và bắt đầu giúp tôi.

AI sẽ tự: cài Git mặc định, kiểm tra WSL2 và tính năng máy ảo (có thể phải khởi động lại máy một lần — AI sẽ dặn bạn gõ `/q` rồi mở lại bằng `omp -c`), cài Docker Desktop nếu thiếu (đến màn hình tạo tài khoản thì cứ bỏ qua, tạo sau), ghi file giới hạn RAM, tải bộ công cụ (khoảng 600 MB), nạp thư viện toán học (khoảng 11 GB, lần đầu có thể hơn một giờ), kiểm tra máy. Trước mỗi bước lâu, AI báo trước làm gì, tại sao, mất bao lâu, và chờ bạn đồng ý. Muốn cài thêm phần mềm nào, AI cũng hỏi trước. Từ lúc AI mở trình cài đặt hay Docker Desktop, AI không nhìn thấy màn hình của bạn — thấy thông báo hay lỗi nào thì copy nguyên văn về cho AI.

## Làm việc hằng ngày

Mỗi lần làm việc: mở **PowerShell**, đi đến thư mục repo trước, rồi mới mở omp:

```powershell
cd Documents\Fermat
omp
```

Thứ tự này quan trọng. omp phải chạy từ trong thư mục repo thì mới thấy file và nhớ việc đang dở.

Lần đầu sau khi dựng máy xong, AI sẽ bảo bạn thoát (`/q`), làm đúng ba dòng trên, rồi nói:

> tiếp tục với chứng minh cho mệnh đề NEW_CONJECTURE.md

Đó là phép thử cuối: giả lập một ngày làm việc bình thường, để chắc mọi thứ chạy được từ trong thư mục repo. Từ đó về sau, mỗi lần mở omp trong thư mục này, bạn chỉ cần nói mình muốn việc nào.

Chuẩn bị sẵn một trong hai thứ:

- File PDF của chứng minh cần kiểm tra (nếu làm việc 1).
- Phát biểu giả thuyết của bạn, viết rõ giả thiết và kết luận (nếu làm việc 2).

Đang chạy mà muốn dừng: bấm **ESC** bất cứ lúc nào.

## Khi có lỗi

- **"Docker ... not running" / "cannot connect"**: mở Docker Desktop, chờ biểu tượng hết quay, thử lại.
- **Máy chậm hoặc báo hết bộ nhớ khi kiểm tra**: tắt các chương trình nặng khác. Mỗi lần chỉ chạy một kiểm tra.
- **Không chạy `docker compose down -v`.** Lệnh này xóa toàn bộ dữ liệu đã tải (hàng GB, phải tải lại). Dừng bình thường chỉ cần `docker compose down`.
- **Lỗi khác**: copy nguyên văn thông báo lỗi gửi cho AI, không cần dịch hay đoán.
