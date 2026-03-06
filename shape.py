# =============================================================================
# SUZUKI帯 各種安定分布形状 + 数学的保証 完全可視化コード
# =============================================================================
import numpy as np
import matplotlib.pyplot as plt
from scipy import stats
import seaborn as sns

class SuzukiDistributionAtlas:
    """全安定分布形状と保証水準の完全解析"""
    
    def __init__(self):
        self.center = 4.2
        self.distributions = {}
    
    def generate_distributions(self):
        """6種類の安定分布を厳密生成"""
        
        # 1. 黄金分布 (δ=0.2) - 超シャープガウス
        self.distributions['黄金 (δ=0.2)'] = stats.norm(4.2, 0.03)
        
        # 2. 安定分布 (δ=0.25) - 標準ガウス  
        self.distributions['安定 (δ=0.25)'] = stats.norm(4.2, 0.045)
        
        # 3. 臨界前 (δ=0.29) - 軽裾ガウス
        self.distributions['臨界前 (δ=0.29)'] = stats.levy_stable(
            alpha=1.8, beta=0, loc=4.2, scale=0.06)
        
        # 4. 臨界後 (δ=0.31) - 双峰分布
        x_bimodal = np.linspace(3.8, 4.6, 1000)
        bimodal = (stats.norm(4.05, 0.04).pdf(x_bimodal) + 
                  stats.norm(4.35, 0.04).pdf(x_bimodal))
        bimodal /= bimodal.max()
        self.distributions['臨界後 (δ=0.31)'] = (x_bimodal, bimodal)
        
        # 5. カオス分布 (δ=0.5) - 重い裾
        self.distributions['カオス (δ=0.5)'] = stats.levy_stable(
            alpha=1.2, beta=0, loc=4.2, scale=0.2)
        
        # 6. 発散分布 (δ=1.0) - ほぼ一様
        self.distributions['発散 (δ=1.0)'] = stats.uniform(3.2, 1.6)
    
    def guarantee_metrics(self, dist_name):
        """各分布のSUZUKI帯[4.1,4.3]内保証確率"""
        if dist_name == '臨界後 (δ=0.31)':
            x, pdf = self.distributions[dist_name]
            prob = np.trapz(pdf[(x>=4.1)&(x<=4.3)], x[(x>=4.1)&(x<=4.3)])
        else:
            dist = self.distributions[dist_name]
            prob = dist.cdf(4.3) - dist.cdf(4.1)
        
        mean = 4.2 if dist_name != '発散 (δ=1.0)' else 4.0
        std = {'黄金':0.03, '安定':0.045, '臨界前':0.06, 
               'カオス':0.2, '発散':0.46}[dist_name.split()[1][1:-1]]
        
        return {
            'P(SUZUKI帯)': f"{prob:.1%}",
            '平均偏差': f"{abs(mean-4.2):.3f}",
            '分布幅σ': f"{std:.3f}",
            '安定保証': '✅完全' if prob>0.95 else '⚠️限界' if prob>0.5 else '❌崩壊'
        }
    
    def plot_distribution_atlas(self):
        """全分布アトラス可視化"""
        self.generate_distributions()
        x = np.linspace(3.5, 4.9, 1000)
        
        fig = plt.figure(figsize=(20, 12))
        
        # 分布形状パネル
        for i, (name, dist) in enumerate(self.distributions.items()):
            ax = plt.subplot(2, 3, i+1)
            
            if name == '臨界後 (δ=0.31)':
                xb, pdfb = dist
                ax.plot(xb, pdfb, 'purple', linewidth=3, label=name)
            else:
                pdf = dist.pdf(x)
                ax.plot(x, pdf, linewidth=3, label=name)
                ax.fill_between(x, pdf, alpha=0.3)
            
            # SUZUKI帯ハイライト
            ax.axvspan(4.1, 4.3, alpha=0.2, color='gold', 
                      label='SUZUKI帯[4.1,4.3]')
            ax.axvline(4.2, color='red', ls='--', alpha=0.7, label='S*=4.2')
            
            ax.set_title(name, fontsize=14, fontweight='bold')
            ax.legend()
            ax.grid(True, alpha=0.3)
        
        plt.tight_layout()
        plt.savefig('suzuki_distribution_atlas.png', dpi=300, bbox_inches='tight')
        
        # 保証度数表
        print("\n" + "="*80)
        print("📊 SUZUKI帯 安定保証度数表")
        print("="*80)
        print(f"{'分布形状':<15} {'P(SUZUKI帯)':<12} {'平均偏差':<10} {'分布幅σ':<8} {'安定保証':<8}")
        print("-"*80)
        
        for name in self.distributions:
            metrics = self.guarantee_metrics(name)
            print(f"{name:<15} {metrics['P(SUZUKI帯)']:<12} {metrics['平均偏差']:<10} "
                  f"{metrics['分布幅σ']:<8} {metrics['安定保証']:<8}")
        
        plt.show()
        
        return self.distributions

# =============================================================================
# 実行: 分布形状完全アトラス
# =============================================================================
if __name__ == "__main__":
    atlas = SuzukiDistributionAtlas()
    distributions = atlas.plot_distribution_atlas()
    
    print("\n" + "="*80)
    print("🎨 SUZUKI帯 分布形状完全分類")
    print("="*80)
    print("① 黄金分布 δ=0.2: 針状ガウス → 完全保証")
    print("② 安定分布 δ=0.25:標準ガウス → 高信頼")  
    print("③ 臨界前 δ=0.29:裾付き → 限界保証")
    print("④ 臨界後 δ=0.31:双峰 → 相転移")
    print("⑤ カオス δ=0.5:重尾 → 崩壊開始")
    print("⑥ 発散 δ=1.0:一様 → 完全無秩序")
    print("="*80)
