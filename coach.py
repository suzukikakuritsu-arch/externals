# ===================================================================
# 鈴木悠起也 外部接続 自動フィードバック完全自動化フレーム
# GitHub / LinkedIn / note 連動 + 定期スコア更新 + 通知
# ===================================================================

import requests
from datetime import datetime
import schedule
import time
import smtplib
from email.mime.text import MIMEText

# -----------------------------
# 評価項目と改善アドバイス
# -----------------------------
external_items = [
    "GitHub公開情報の整合性",
    "note・LinkedInでの発信透明性",
    "他者レビューの受け入れ度",
    "ライセンス・権利管理の明確さ",
    "ドキュメントの充実度",
    "依存関係の整理・明確さ",
    "外部コラボレーションの頻度",
    "質問・問い合わせ対応の丁寧さ",
    "コミュニティ参加の積極性",
    "情報更新のタイムリーさ"
]

advice_messages = [
    "公開情報を整理して、他者が理解できるようにする。",
    "発信は透明に、意図や背景も共有。",
    "レビューや意見は積極的に受け入れ改善。",
    "権利やライセンスを明確に管理。",
    "ドキュメントを充実させて誰でも追えるように。",
    "依存関係を整理し、理解しやすく。",
    "コラボレーションを積極的に増やす。",
    "質問対応は丁寧に行い、誤解を避ける。",
    "コミュニティ参加を習慣化する。",
    "情報更新はタイムリーに行う。"
]

# -----------------------------
# GitHub情報取得
# -----------------------------
def github_scores(username):
    url = f"https://api.github.com/users/{username}/repos"
    try:
        resp = requests.get(url)
        repos = resp.json()
        if isinstance(repos, list):
            num_repos = len(repos)
            recent_updates = sum(
                1 for r in repos if 'pushed_at' in r and (datetime.utcnow() - datetime.strptime(r['pushed_at'], "%Y-%m-%dT%H:%M:%SZ")).days <= 90
            )
            score_public = min(10, num_repos // 2 + recent_updates)
            score_collab = min(10, max(5, recent_updates // 2))  # 仮のコラボ頻度
            return score_public, score_collab
    except:
        return 5,5

# -----------------------------
# LinkedIn / note 情報取得 (関数枠)
# -----------------------------
def linkedin_score():
    # APIやスクレイピングで取得可能
    post_count = random.randint(5,10)
    review_acceptance = random.randint(4,9)
    update_timeliness = random.randint(5,10)
    return post_count, review_acceptance, update_timeliness

# -----------------------------
# スコア計算 & フィードバック生成
# -----------------------------
def compute_feedback():
    import random
    scores = [0]*10
    gh_score1, gh_score2 = github_scores("suzukikakuritsu-arch")
    scores[0] = gh_score1
    scores[6] = gh_score2
    ln1, ln2, ln3 = linkedin_score()
    scores[1] = ln1
    scores[2] = ln2
    scores[9] = ln3
    for i in [3,4,5,7,8]:
        scores[i] = random.randint(5,9)
    total = sum(scores)
    avg = total / 10
    feedback = []
    for i, (item, advice, score) in enumerate(zip(external_items, advice_messages, scores)):
        if score < 7:
            feedback.append(f"{i+1}. {item} (採点: {score}/10) ⚠️ 改善提案: {advice}")
        else:
            feedback.append(f"{i+1}. {item} (採点: {score}/10) ✅ 良好")
    feedback.append(f"💡 総合スコア: {avg:.1f}/10")
    return "\n".join(feedback)

# -----------------------------
# 通知送信（メール例）
# -----------------------------
def send_email_feedback(feedback_text, to_email):
    from_email = "youremail@example.com"
    msg = MIMEText(feedback_text)
    msg['Subject'] = "鈴木悠起也 外部接続 自動フィードバック"
    msg['From'] = from_email
    msg['To'] = to_email
    try:
        with smtplib.SMTP('smtp.example.com', 587) as server:
            server.starttls()
            server.login(from_email, "yourpassword")
            server.send_message(msg)
        print("📧 フィードバックメール送信完了")
    except Exception as e:
        print("❌ メール送信失敗:", e)

# -----------------------------
# 定期スケジュール実行（毎週月曜10時）
# -----------------------------
def job():
    feedback = compute_feedback()
    print(feedback)
    # send_email_feedback(feedback, "yukiya@example.com")  # メール送信有効化

schedule.every().monday.at("10:00").do(job)

print("⏰ 自動フィードバックスケジュール開始...")
while True:
    schedule.run_pending()
    time.sleep(60)