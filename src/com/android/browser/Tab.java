/*
 * Copyright (C) 2009 The Android Open Source Project
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package com.android.browser;

import android.app.Activity;
import android.app.AlertDialog;
import android.content.ContentResolver;
import android.content.ContentValues;
import android.content.Context;
import android.content.DialogInterface;
import android.content.DialogInterface.OnCancelListener;
import android.content.pm.PackageManager;
import android.graphics.Bitmap;
import android.graphics.Bitmap.CompressFormat;
import android.graphics.BitmapFactory;
import android.graphics.Canvas;
import android.graphics.Color;
import android.graphics.Paint;
import android.graphics.Picture;
import android.graphics.PorterDuff;
import android.graphics.PorterDuffXfermode;
import android.net.Uri;
import android.net.http.SslError;
import android.os.Bundle;
import android.os.Handler;
import android.os.Message;
import android.os.SystemClock;
import android.security.KeyChain;
import android.security.KeyChainAliasCallback;
import android.text.TextUtils;
import android.util.Log;
import android.view.KeyEvent;
import android.view.LayoutInflater;
import android.view.View;
import android.view.ViewStub;
import android.webkit.ClientCertRequest;
import android.webkit.ConsoleMessage;
import android.webkit.CookieManager;
import android.webkit.GeolocationPermissions;
import android.webkit.GeolocationPermissions.Callback;
import android.webkit.HttpAuthHandler;
import android.webkit.JsPromptResult;
import android.webkit.JsResult;
import android.webkit.PermissionRequest;
import android.webkit.SslErrorHandler;
import android.webkit.URLUtil;
import android.webkit.ValueCallback;
import android.webkit.WebBackForwardList;
import android.webkit.WebChromeClient;
import android.webkit.WebChromeClient.FileChooserParams;
import android.webkit.WebHistoryItem;
import android.webkit.WebResourceResponse;
import android.webkit.WebStorage;
import android.webkit.WebView;
import android.webkit.WebView.PictureListener;
import android.webkit.WebViewClient;
import android.widget.CheckBox;
import android.widget.Toast;

import com.android.browser.TabControl.OnThumbnailUpdatedListener;
import com.android.browser.homepages.HomeProvider;
import com.android.browser.provider.SnapshotProvider.Snapshots;

import java.io.ByteArrayOutputStream;
import java.io.ByteArrayInputStream;
import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.nio.ByteBuffer;
import java.security.Principal;
import java.util.LinkedList;
import java.util.Map;
import java.util.UUID;
import java.util.Vector;
import java.util.regex.Pattern;
import java.util.zip.GZIPOutputStream;

/**
 * Class for maintaining Tabs with a main WebView and a subwindow.
 */
class Tab implements PictureListener {

    // Log Tag
    private static final String LOGTAG = "Tab";
    private static final boolean LOGD_ENABLED = com.android.browser.Browser.LOGD_ENABLED;
    // Special case the logtag for messages for the Console to make it easier to
    // filter them and match the logtag used for these messages in older versions
    // of the browser.
    private static final String CONSOLE_LOGTAG = "browser";

    private static final int MSG_CAPTURE = 42;
    private static final int CAPTURE_DELAY = 100;
    private static final int INITIAL_PROGRESS = 5;
    private static final String RESTRICTED = "<html><body>not allowed</body></html>";

    private static Bitmap sDefaultFavicon;

    private static Paint sAlphaPaint = new Paint();
    static {
        sAlphaPaint.setXfermode(new PorterDuffXfermode(PorterDuff.Mode.CLEAR));
        sAlphaPaint.setColor(Color.TRANSPARENT);
    }

    public enum SecurityState {
        // The page's main resource does not use SSL. Note that we use this
        // state irrespective of the SSL authentication state of sub-resources.
        SECURITY_STATE_NOT_SECURE,
        // The page's main resource uses SSL and the certificate is good. The
        // same is true of all sub-resources.
        SECURITY_STATE_SECURE,
        // The page's main resource uses SSL and the certificate is good, but
        // some sub-resources either do not use SSL or have problems with their
        // certificates.
        SECURITY_STATE_MIXED,
        // The page's main resource uses SSL but there is a problem with its
        // certificate.
        SECURITY_STATE_BAD_CERTIFICATE,
    }

    Context mContext;
    protected WebViewController mWebViewController;

    // The tab ID
    private long mId = -1;

    // The Geolocation permissions prompt
    private GeolocationPermissionsPrompt mGeolocationPermissionsPrompt;
    // The permissions prompt
    private PermissionsPrompt mPermissionsPrompt;
    // Main WebView wrapper
    private View mContainer;
    // Main WebView
    private WebView mMainView;
    // Subwindow container
    private View mSubViewContainer;
    // Subwindow WebView
    private WebView mSubView;
    // Saved bundle for when we are running low on memory. It contains the
    // information needed to restore the WebView if the user goes back to the
    // tab.
    private Bundle mSavedState;
    // Parent Tab. This is the Tab that created this Tab, or null if the Tab was
    // created by the UI
    private Tab mParent;
    // Tab that constructed by this Tab. This is used when this Tab is
    // destroyed, it clears all mParentTab values in the children.
    private Vector<Tab> mChildren;
    // If true, the tab is in the foreground of the current activity.
    private boolean mInForeground;
    // If true, the tab is in page loading state (after onPageStarted,
    // before onPageFinsihed)
    private boolean mInPageLoad;
    private boolean mDisableOverrideUrlLoading;
    // If true, the current page is the most visited page
    private boolean mInMostVisitedPage;
    // The last reported progress of the current page
    private int mPageLoadProgress;
    // The time the load started, used to find load page time
    private long mLoadStartTime;
    // Application identifier used to find tabs that another application wants
    // to reuse.
    private String mAppId;
    // flag to indicate if tab should be closed on back
    private boolean mCloseOnBack;
    // Keep the original url around to avoid killing the old WebView if the url
    // has not changed.
    // Error console for the tab
    private ErrorConsoleView mErrorConsole;
    // The listener that gets invoked when a download is started from the
    // mMainView
    private final BrowserDownloadListener mDownloadListener;
    // Listener used to know when we move forward or back in the history list.
    private final WebBackForwardListClient mWebBackForwardListClient;
    private DataController mDataController;
    // State of the auto-login request.
    private DeviceAccountLogin mDeviceAccountLogin;

    // AsyncTask for downloading touch icons
    DownloadTouchIcon mTouchIconLoader;

    private BrowserSettings mSettings;
    private int mCaptureWidth;
    private int mCaptureHeight;
    private Bitmap mCapture;
    private Handler mHandler;
    private boolean mUpdateThumbnail;

    /**
     * See {@link #clearBackStackWhenItemAdded(String)}.
     */
    private Pattern mClearHistoryUrlPattern;

    private static synchronized Bitmap getDefaultFavicon(Context context) {
        if (sDefaultFavicon == null) {
            sDefaultFavicon = BitmapFactory.decodeResource(
                    context.getResources(), R.drawable.app_web_browser_sm);
        }
        return sDefaultFavicon;
    }

    // All the state needed for a page
    protected static class PageState {
        String mUrl;
        String mOriginalUrl;
        String mTitle;
        SecurityState mSecurityState;
        // This is non-null only when mSecurityState is SECURITY_STATE_BAD_CERTIFICATE.
        SslError mSslCertificateError;
        Bitmap mFavicon;
        boolean mIsBookmarkedSite;
        boolean mIncognito;

        PageState(Context c, boolean incognito) {
            mIncognito = incognito;
            if (mIncognito) {
                mOriginalUrl = mUrl = "browser:incognito";
                mTitle = c.getString(R.string.new_incognito_tab);
            } else {
                mOriginalUrl = mUrl = "";
                mTitle = c.getString(R.string.new_tab);
            }
            mSecurityState = SecurityState.SECURITY_STATE_NOT_SECURE;
        }

        PageState(Context c, boolean incognito, String url, Bitmap favicon) {
            mIncognito = incognito;
            mOriginalUrl = mUrl = url;
            if (URLUtil.isHttpsUrl(url)) {
                mSecurityState = SecurityState.SECURITY_STATE_SECURE;
            } else {
                mSecurityState = SecurityState.SECURITY_STATE_NOT_SECURE;
            }
            mFavicon = favicon;
        }

    }

    // The current/loading page's state
    protected PageState mCurrentState;

    // Used for saving and restoring each Tab
    static final String ID = "ID";
    static final String CURRURL = "currentUrl";
    static final String CURRTITLE = "currentTitle";
    static final String PARENTTAB = "parentTab";
    static final String APPID = "appid";
    static final String INCOGNITO = "privateBrowsingEnabled";
    static final String USERAGENT = "useragent";
    static final String CLOSEFLAG = "closeOnBack";

    // Container class for the next error dialog that needs to be displayed
    private class ErrorDialog {
        public final int mTitle;
        public final String mDescription;
        public final int mError;
        ErrorDialog(int title, String desc, int error) {
            mTitle = title;
            mDescription = desc;
            mError = error;
        }
    }

    private void processNextError() {
        if (mQueuedErrors == null) {
            return;
        }
        // The first one is currently displayed so just remove it.
        mQueuedErrors.removeFirst();
        if (mQueuedErrors.size() == 0) {
            mQueuedErrors = null;
            return;
        }
        showError(mQueuedErrors.getFirst());
    }

    private DialogInterface.OnDismissListener mDialogListener =
            new DialogInterface.OnDismissListener() {
                public void onDismiss(DialogInterface d) {
                    processNextError();
                }
            };
    private LinkedList<ErrorDialog> mQueuedErrors;

    private void queueError(int err, String desc) {
        if (mQueuedErrors == null) {
            mQueuedErrors = new LinkedList<ErrorDialog>();
        }
        for (ErrorDialog d : mQueuedErrors) {
            if (d.mError == err) {
                // Already saw a similar error, ignore the new one.
                return;
            }
        }
        ErrorDialog errDialog = new ErrorDialog(
                err == WebViewClient.ERROR_FILE_NOT_FOUND ?
                R.string.browserFrameFileErrorLabel :
                R.string.browserFrameNetworkErrorLabel,
                desc, err);
        mQueuedErrors.addLast(errDialog);

        // Show the dialog now if the queue was empty and it is in foreground
        if (mQueuedErrors.size() == 1 && mInForeground) {
            showError(errDialog);
        }
    }

    private void showError(ErrorDialog errDialog) {
        if (mInForeground) {
            AlertDialog d = new AlertDialog.Builder(mContext)
                    .setTitle(errDialog.mTitle)
                    .setMessage(errDialog.mDescription)
                    .setPositiveButton(R.string.ok, null)
                    .create();
            d.setOnDismissListener(mDialogListener);
            d.show();
        }
    }

    // -------------------------------------------------------------------------
    // WebViewClient implementation for the main WebView
    // -------------------------------------------------------------------------

    private final WebViewClient mWebViewClient = new WebViewClient() {
        private Message mDontResend;
        private Message mResend;

        private boolean providersDiffer(String url, String otherUrl) {
            Uri uri1 = Uri.parse(url);
            Uri uri2 = Uri.parse(otherUrl);
            return !uri1.getEncodedAuthority().equals(uri2.getEncodedAuthority());
        }

        @Override
        public void onPageStarted(WebView view, String url, Bitmap favicon) {
            mInPageLoad = true;
            mUpdateThumbnail = true;
            mPageLoadProgress = INITIAL_PROGRESS;
            mCurrentState = new PageState(mContext,
                    view.isPrivateBrowsingEnabled(), url, favicon);
            mLoadStartTime = SystemClock.uptimeMillis();

            if (isPrivateBrowsingEnabled()) {
                // Ignore all the cookies while an incognito tab has activity
                CookieManager.getInstance().setAcceptCookie(false);
            }

            // If we start a touch icon load and then load a new page, we don't
            // want to cancel the current touch icon loader. But, we do want to
            // create a new one when the touch icon url is known.
            if (mTouchIconLoader != null) {
                mTouchIconLoader.mTab = null;
                mTouchIconLoader = null;
            }

            // reset the error console
            if (mErrorConsole != null) {
                mErrorConsole.clearErrorMessages();
                if (mWebViewController.shouldShowErrorConsole()) {
                    mErrorConsole.showConsole(ErrorConsoleView.SHOW_NONE);
                }
            }

            // Cancel the auto-login process.
            if (mDeviceAccountLogin != null) {
                mDeviceAccountLogin.cancel();
                mDeviceAccountLogin = null;
                mWebViewController.hideAutoLogin(Tab.this);
            }

            // finally update the UI in the activity if it is in the foreground
            mWebViewController.onPageStarted(Tab.this, view, favicon);

            updateBookmarkedStatus();
        }

        @Override
        public void onPageFinished(WebView view, String url) {
            mDisableOverrideUrlLoading = false;
            if (!isPrivateBrowsingEnabled()) {
                LogTag.logPageFinishedLoading(
                        url, SystemClock.uptimeMillis() - mLoadStartTime);
            } else {
                // Ignored all the cookies while an incognito tab had activity,
                // restore default after completion
                CookieManager.getInstance().setAcceptCookie(mSettings.acceptCookies());
            }
            syncCurrentState(view, url);
            mWebViewController.onPageFinished(Tab.this);

            if (mCurrentState.mUrl.equals(HomeProvider.MOST_VISITED_URL)) {
                if (!mInMostVisitedPage) {
                    loadUrl(HomeProvider.MOST_VISITED, null);
                    mInMostVisitedPage = true;
                }
                view.clearHistory();
            } else {
                mInMostVisitedPage = false;
            }
        }

        // return true if want to hijack the url to let another app to handle it
        @Override
        public boolean shouldOverrideUrlLoading(WebView view, String url) {
            if (!mDisableOverrideUrlLoading && mInForeground) {
                return mWebViewController.shouldOverrideUrlLoading(Tab.this,
                        view, url);
            } else {
                return false;
            }
        }

        /**
         * Updates the security state. This method is called when we discover
         * another resource to be loaded for this page (for example,
         * javascript). While we update the security state, we do not update
         * the lock icon until we are done loading, as it is slightly more
         * secure this way.
         */
        @Override
        public void onLoadResource(WebView view, String url) {
            if (url != null && url.length() > 0) {
                // It is only if the page claims to be secure that we may have
                // to update the security state:
                if (mCurrentState.mSecurityState == SecurityState.SECURITY_STATE_SECURE) {
                    // If NOT a 'safe' url, change the state to mixed content!
                    if (!(URLUtil.isHttpsUrl(url) || URLUtil.isDataUrl(url)
                            || URLUtil.isAboutUrl(url))) {
                        mCurrentState.mSecurityState = SecurityState.SECURITY_STATE_MIXED;
                    }
                }
            }
        }

        /**
         * Show a dialog informing the user of the network error reported by
         * WebCore if it is in the foreground.
         */
        @Override
        public void onReceivedError(WebView view, int errorCode,
                String description, String failingUrl) {
            if (errorCode != WebViewClient.ERROR_HOST_LOOKUP &&
                    errorCode != WebViewClient.ERROR_CONNECT &&
                    errorCode != WebViewClient.ERROR_BAD_URL &&
                    errorCode != WebViewClient.ERROR_UNSUPPORTED_SCHEME &&
                    errorCode != WebViewClient.ERROR_FILE) {
                queueError(errorCode, description);

                // Don't log URLs when in private browsing mode
                if (!isPrivateBrowsingEnabled()) {
                    Log.e(LOGTAG, "onReceivedError " + errorCode + " " + failingUrl
                        + " " + description);
                }
            }
        }

        /**
         * Check with the user if it is ok to resend POST data as the page they
         * are trying to navigate to is the result of a POST.
         */
        @Override
        public void onFormResubmission(WebView view, final Message dontResend,
                                       final Message resend) {
            if (!mInForeground) {
                dontResend.sendToTarget();
                return;
            }
            if (mDontResend != null) {
                Log.w(LOGTAG, "onFormResubmission should not be called again "
                        + "while dialog is still up");
                dontResend.sendToTarget();
                return;
            }
            mDontResend = dontResend;
            mResend = resend;
            new AlertDialog.Builder(mContext).setTitle(
                    R.string.browserFrameFormResubmitLabel).setMessage(
                    R.string.browserFrameFormResubmitMessage)
                    .setPositiveButton(R.string.ok,
                            new DialogInterface.OnClickListener() {
                                public void onClick(DialogInterface dialog,
                                        int which) {
                                    if (mResend != null) {
                                        mResend.sendToTarget();
                                        mResend = null;
                                        mDontResend = null;
                                    }
                                }
                            }).setNegativeButton(R.string.cancel,
                            new DialogInterface.OnClickListener() {
                                public void onClick(DialogInterface dialog,
                                        int which) {
                                    if (mDontResend != null) {
                                        mDontResend.sendToTarget();
                                        mResend = null;
                                        mDontResend = null;
                                    }
                                }
                            }).setOnCancelListener(new OnCancelListener() {
                        public void onCancel(DialogInterface dialog) {
                            if (mDontResend != null) {
                                mDontResend.sendToTarget();
                                mResend = null;
                                mDontResend = null;
                            }
                        }
                    }).show();
        }

        /**
         * Insert the url into the visited history database.
         * @param url The url to be inserted.
         * @param isReload True if this url is being reloaded.
         * FIXME: Not sure what to do when reloading the page.
         */
        @Override
        public void doUpdateVisitedHistory(WebView view, String url,
                boolean isReload) {
            mWebViewController.doUpdateVisitedHistory(Tab.this, isReload);
        }

        /**
         * Displays SSL error(s) dialog to the user.
         */
        @Override
        public void onReceivedSslError(final WebView view,
                final SslErrorHandler handler, final SslError error) {
            if (!mInForeground) {
                handler.cancel();
                setSecurityState(SecurityState.SECURITY_STATE_NOT_SECURE);
                return;
            }
            if (mSettings.showSecurityWarnings()) {
                new AlertDialog.Builder(mContext)
                    .setTitle(R.string.security_warning)
                    .setMessage(R.string.ssl_warnings_header)
                    .setIconAttribute(android.R.attr.alertDialogIcon)
                    .setPositiveButton(R.string.ssl_continue,
                        new DialogInterface.OnClickListener() {
                            @Override
                            public void onClick(DialogInterface dialog,
                                    int whichButton) {
                                handler.proceed();
                                handleProceededAfterSslError(error);
                            }
                        })
                    .setNeutralButton(R.string.view_certificate,
                        new DialogInterface.OnClickListener() {
                            @Override
                            public void onClick(DialogInterface dialog,
                                    int whichButton) {
                                mWebViewController.showSslCertificateOnError(
                                        view, handler, error);
                            }
                        })
                    .setNegativeButton(R.string.ssl_go_back,
                        new DialogInterface.OnClickListener() {
                            @Override
                            public void onClick(DialogInterface dialog,
                                    int whichButton) {
                                dialog.cancel();
                            }
                        })
                    .setOnCancelListener(
                        new DialogInterface.OnCancelListener() {
                            @Override
                            public void onCancel(DialogInterface dialog) {
                                handler.cancel();
                                setSecurityState(SecurityState.SECURITY_STATE_NOT_SECURE);
                                mWebViewController.onUserCanceledSsl(Tab.this);
                            }
                        })
                    .show();
            } else {
                handler.proceed();
                handleProceededAfterSslError(error);
            }
        }

        /**
         * Displays client certificate request to the user.
         */
        @Override
        public void onReceivedClientCertRequest(final WebView view,
                final ClientCertRequest request) {
            if (!mInForeground) {
                request.ignore();
                return;
            }
            KeyChain.choosePrivateKeyAlias(
                    mWebViewController.getActivity(), new KeyChainAliasCallback() {
                @Override public void alias(String alias) {
                    if (alias == null) {
                        request.cancel();
                        return;
                    }
                    new KeyChainLookup(mContext, request, alias).execute();
                }
            }, request.getKeyTypes(), request.getPrincipals(), request.getHost(),
                request.getPort(), null);
        }

       /**
         * Handles an HTTP authentication request.
         *
         * @param handler The authentication handler
         * @param host The host
         * @param realm The realm
         */
        @Override
        public void onReceivedHttpAuthRequest(WebView view,
                final HttpAuthHandler handler, final String host,
                final String realm) {
            mWebViewController.onReceivedHttpAuthRequest(Tab.this, view, handler, host, realm);
        }

        // Adblocking from URL lists from world added by
        protected boolean isBlockedSite(String url) {
      //    String url = uri.toString();
        Uri uri = Uri.parse(url);
        String host = uri.getHost();
//              boolean useMostVisited = BrowserSettings.getInstance().useMostVisitedHomepage();
//          String[] GS = GeneralPreferencesFragment.getInstance().mGoogleSites();
        String[] blockedSites = {
		"disqus.com",
		"internet.org",
		"facebook.com",
		"facebook.com.br",
		"facebook.net",
		"facebook.fr",
		"facebook.de",
		"facebook.dk",
		"fb.com",
		"m.me",
		"fb.me",
		"fbcdn.net",
		"fbcdn.com",
		"tfbnw.net",
		"instagram.com",
		"cdninstagram.com",
		"messenger.com",
		"whatsapp.com",
		"momentsapp.com",
		"edgekey.net",
		"edgesuite.net",
		"metrix.net",
		"fbfansite.com",
		"facebook.org.uk",
		"facebook.hu",
		"ff.gg",
		"thefacebook.hu",
		"facebook.net.pk",
		"facebook.com.sv",
		"facebook.eu",
		"socialgraph.fr",
		"fbsbx.com",
		"mywapblog.co",
		"baijee.tw",
		"frebasix.com",
		"tyvpn.cn",
		"farmers-grill.om",
		"facebookformobileoperators.com",
		"facebookinc.com",
		"facebook-inc.com",
		"connectlife.xyz",
		"fbhome.co.uk",
		"freebasic.com",
		"frebasics.com",
		"freebasics.com",
		"fbasics.com",
		"freeb.com",
		"freebs.com",
		"freeb6.com",
		"freebasik.com",
		"frebasik.com",
		"frebasiks.com",
		"centralpixel.org",
		"messengerfordesktop.com",
		"messengerblog.com",
		"0.google.com",
		"100.net",
		"1.google.com",
		"2.google.com",
		"3.google.com",
		"466453.com",
		"4.google.com",
		"5.google.com",
		"6.google.com",
		"7.google.com",
		"8.google.com",
		"9.google.com",
		"accounts.google.com",
		"admob.com",
		"adsense.com",
		"adwords.com",
		"android.com",
		"apis.google.com",
		"blogger.com",
		"blogspot.com",
		"cache.google.com",
		"chromebook.com",
		"chrome.com",
		"chrome.google.com",
		"chromium.org",
		"cobrasearch.com",
		"com.google",
		"developers.google.com",
		"dl.google.com",
		"docs.google.com",
		"domains.google",
		"doubleclickbygoogle.com",
		"doubleclick.com",
		"doubleclick.net",
		"drive.google.com",
		"duck.com",
		"firehunt.com",
		"foofle.com",
		"froogle.com",
		"fusion.google.com",
		"g.cn",
		"g.co",
		"ggoogle.com",
		"ggpht.com",
		"ghs.google.com",
		"gmail.com",
		"gmodules.com",
		"gogle.com",
		"gogole.com",
		"googel.com",
		"googil.com",
		"goo.gl",
		"googl.com",
		"google",
		"google.ac",
		"google.ad",
		"googleadservices.com",
		"google.ae",
		"google.al",
		"google.am",
		"google-analytics.com",
		"googleanalytics.com",
		"googleapis.com",
		"googleapps.com",
		"googlearth.com",
		"google.as",
		"google.at",
		"google.az",
		"google.ba",
		"google.be",
		"google.bf",
		"google.bg",
		"google.bi",
		"google.bj",
		"googlebot.com",
		"google.bs",
		"google.bt",
		"google.by",
		"google.ca",
		"google.cat",
		"google.cc",
		"google.cd",
		"google.cf",
		"google.cg",
		"google.ch",
		"google.ci",
		"google.cl",
		"google.cm",
		"google.cn",
		"google.co.ao",
		"google.co.bw",
		"google.co.ck",
		"google.co.cr",
		"googlecode.com",
		"google.co.hu",
		"google.co.id",
		"google.co.il",
		"google.co.im",
		"google.co.in",
		"google.co.je",
		"google.co.jp",
		"google.co.ke",
		"google.co.kr",
		"google.co.ls",
		"google.com",
		"google.co.ma",
		"google.com.af",
		"google.com.ag",
		"google.com.ai",
		"google.com.ar",
		"google.com.au",
		"google.com.bd",
		"google.com.bh",
		"google.com.bn",
		"google.com.bo",
		"google.com.br",
		"google.com.bz",
		"google.com.co",
		"google.com.cu",
		"google.com.cy",
		"google.com.do",
		"google.com.ec",
		"google.com.eg",
		"google.com.et",
		"google.com.fj",
		"google.com.gh",
		"google.com.gi",
		"google.com.gt",
		"google.com.hk",
		"google.com.jm",
		"google.com.kh",
		"google.com.kw",
		"google.com.lb",
		"google.com.lc",
		"google.com.ly",
		"googlecommerce.com",
		"google.com.mm",
		"google.com.mt",
		"google.com.mx",
		"google.com.my",
		"google.com.na",
		"google.com.nf",
		"google.com.ng",
		"google.com.ni",
		"google.com.np",
		"google.com.om",
		"google.com.pa",
		"google.com.pe",
		"google.com.pg",
		"google.com.ph",
		"google.com.pk",
		"google.com.pr",
		"google.com.py",
		"google.com.qa",
		"google.com.sa",
		"google.com.sb",
		"google.com.sg",
		"google.com.sl",
		"google.com.sv",
		"google.com.tj",
		"google.com.tr",
		"google.com.tw",
		"google.com.ua",
		"google.com.uy",
		"google.com.uz",
		"google.com.vc",
		"google.com.vn",
		"google.co.mz",
		"google.co.nz",
		"google.co.th",
		"google.co.tz",
		"google.co.ug",
		"google.co.uk",
		"google.co.uz",
		"google.co.ve",
		"google.co.vi",
		"google.co.za",
		"google.co.zm",
		"google.co.zw",
		"google.cv",
		"google.cz",
		"google.de",
		"google.dj",
		"google.dk",
		"google.dm",
		"googledrive.com",
		"google.dz",
		"googleearth.com",
		"googlee.com",
		"google.ee",
		"google.es",
		"google.fi",
		"google.fm",
		"google.fr",
		"google.ga",
		"google.ge",
		"google.gf",
		"google.gg",
		"google.gl",
		"google.gm",
		"google.gp",
		"google.gr",
		"googlegroups.com",
		"google.gy",
		"google.hn",
		"google.hr",
		"google.ht",
		"google.hu",
		"google.ie",
		"google.im",
		"google.io",
		"google.iq",
		"google.is",
		"google.it",
		"google.je",
		"google.jo",
		"google.kg",
		"google.ki",
		"google.kz",
		"google.la",
		"google.li",
		"google.lk",
		"google.lt",
		"google.lu",
		"google.lv",
		"googlemail.com",
		"googlemaps.com",
		"google.md",
		"google.me",
		"googlemember.com",
		"googlemembers.com",
		"google.mg",
		"google.mk",
		"google.ml",
		"google.mn",
		"google.ms",
		"google.mu",
		"google.mv",
		"google.mw",
		"google.ne",
		"google.net",
		"google.nl",
		"google.no",
		"google.nr",
		"google.nu",
		"google.off.ai",
		"google.org",
		"googlepagecreator.com",
		"google.pl",
		"google.pn",
		"google.ps",
		"google.pt",
		"google.ro",
		"google.rs",
		"google.ru",
		"google.rw",
		"google.sc",
		"googlescholar.com",
		"google.se",
		"google.sh",
		"google.si",
		"google.sk",
		"google.sm",
		"google.sn",
		"google.so",
		"googlesource.com",
		"google.sr",
		"google.st",
		"googlesyndication.com",
		"googletagmanager.com",
		"googletagservices.com",
		"google.td",
		"google.tg",
		"google.tk",
		"google.tl",
		"google.tm",
		"google.tn",
		"google.to",
		"google.tp",
		"google.tt",
		"google.tv",
		"googleusercontent.com",
		"google.uz",
		"google.vg",
		"google.vu",
		"google.ws",
		"googlr.com",
		"goolge.com",
		"gooogle.com",
		"groups.google.com",
		"gstatic.com",
		"gstatic.info",
		"gvt1.com",
		"gvt2.com",
		"igoogle.com",
		"keyhole.com",
		"like.com",
		"madewithcode.com",
		"mail.google.com",
		"maps.google.com",
		"pack.google.com",
		"panoramio.com",
		"picasa.com",
		"plus.google.com",
		"plusone.google.com",
		"safebrowsing.google.com",
		"sb.google.com",
		"sketchup.com",
		"ssl.google.com",
		"tools.google.com",
		"translate.google.com",
		"urchin.com",
		"waze.com",
		"whatbrowser.org",
		"withgoogle.com",
		"youtube-nocookie.com",
		"thinkwithgoogle.com",
		"safebrowsing.google.com",
		"sb-ssl.google.com",
                "0000mps.webpreview.dsl.net",
		"0001.2waky.com",
		"001wen.com",
		"00game.net",
		"01cn.net",
		"021id.net",
		"022sy.com",
		"025zd.com",
		"027i.com",
		"029999.com",
		"0377.wang",
		"0470y.com",
		"0511zfhl.com",
		"0512px.net",
		"0538ly.cn",
		"0551fs.com",
		"0559edu.com",
		"05711.cn",
		"0571jjw.com",
		"0571seoer.com",
		"0571zxw.com",
		"0574-office.com",
		"0579i.cn",
		"0632qyw.com",
		"071899.com",
		"07353.com",
		"0735sh.com",
		"0743j.com",
		"0755hsl.com",
		"0755model.com",
		"0766ldzx.com",
		"0769sms.com",
		"0772it.net",
		"0797fdc.com.cn",
		"0820.com",
		"086pop.com",
		"08819.com",
		"0932mls.com",
		"0971pkw.com",
		"099499.com",
		"0995114.net",
		"09cd.co.kr",
		"09zyy.com",
		"10086hyl.com",
		"100jzyx.com",
		"1010fz.com",
		"101.boquan.net",
		"101com.com",
		"101order.com",
		"107rust.com",
		"10eurosbonheur.org",
		"111yc.com",
		"1146qt.com",
		"1147.org",
		"1149.a38q.cn",
		"114oldest.com",
		"114.sohenan.cn",
		"114y.net",
		"119ye.com",
		"123188.com",
		"123found.com",
		"124dy.net",
		"125668.csmes.org",
		"125jia.cn",
		"125jumeinv.com",
		"13148990763.com",
		"137311.com",
		"138771.com",
		"13903825045.com",
		"140game.com",
		"140proof.com",
		"14198.com",
		"14h.pw",
		"173okwei.com",
		"173usdy.com",
		"17511.com",
		"175hd.com",
		"177llll.com",
		"177momo.com",
		"1788111.com",
		"17sise.com",
		"17so.so",
		"180hits.de",
		"180searchassistant.com",
		"181851.30la.com.cn",
		"18818879699.com",
		"189y.com",
		"18cum.com",
		"18dd.net",
		"18xn.com",
		"191gm.com",
		"19degrees.org",
		"19free.org",
		"19xs.com",
		"1a-teensbilder.de",
		"1e1v.com",
		"1egy.com",
		"1phua.com",
		"1pu1.com",
		"1qingling.com",
		"1stand2ndmortgage.com",
		"1x1rank.com",
		"1yyju.com",
		"2000tours.com",
		"2012ui.com",
		"201ddlyh.com",
		"207.net",
		"20ro.com",
		"247media.com",
		"24aspx.com",
		"24corp-shop.com",
		"24jingxuan.com",
		"24log.com",
		"24log.de",
		"24pm-affiliation.com",
		"24-verygoods.ru",
		"24xiaz5ai.cn",
		"2666120.com",
		"27mn.com",
		"27simn888.com",
		"2mdn.net",
		"2ndzenith.com",
		"2o7.net",
		"308888.com",
		"318x.com",
		"31qqww.com",
		"3231198.com",
		"3231.cc",
		"3262111.com",
		"32hy.com",
		"330824.com",
		"33246.net",
		"332gm.com",
		"33kkvv.com",
		"33lzmm.com",
		"33nn.com",
		"345hc.com",
		"360dfc.com",
		"360yield.com",
		"36219.net",
		"36438.com",
		"365rebo.com",
		"365tc.com",
		"36robots.com",
		"371678.com",
		"384756783900.cn",
		"38zu.cn",
		"39m.net",
		"3cinteractive.com",
		"3dmv.net",
		"3dubo.com",
		"3e3ex8zr4.cnrdn.com",
		"3fgt.com",
		"3gmission.com",
		"3omrelk.com",
		"3sixtyventure.com",
		"3xstuff.com",
		"3years.lethanon.net",
		"3yyj.cn",
		"4000506708.com",
		"4004.cn",
		"4006868488.cn",
		"400cao.com",
		"43242.com",
		"44cckk.com",
		"44ccvv.com",
		"44xxdd.com",
		"488568.com",
		"4affiliate.net",
		"4analytics.ws",
		"4chan-tube.on.nimp.org",
		"4d5.net",
		"4info.com",
		"4mads.com",
		"4pda-ru.ru",
		"4safe.in",
		"4sshouhou.com",
		"5000444.com",
		"50websads.com",
		"510w.com",
		"51156434.swh.strato-hosting.eu",
		"511hs.com",
		"5123.ru",
		"5151ac.com",
		"5178424.com",
		"518ad.com",
		"518zihui.com",
		"51daima.com",
		"51huanche.com",
		"51hzmn.com",
		"51jczxw.com",
		"51lvyu.com",
		"51mogui.com",
		"51sedy.com",
		"51she.info",
		"51winjob.net",
		"51winjob.org",
		"51xcedu.com",
		"51xingming.com",
		"51yes.com",
		"51yirong.com",
		"51youhua.org",
		"51ysxs.com",
		"51zc.cc",
		"51zhongguo.com",
		"5233w.net",
		"52bikes.com",
		"52cfw.com",
		"52djcy.com",
		"52esport.com",
		"52flz.com",
		"52porn.net",
		"54bet.com",
		"54fangtan.com",
		"54ly.com",
		"54te.com",
		"55511b.com",
		"563tm.com",
		"5678uc.com",
		"567bbl.com",
		"5683.com",
		"5689.nl",
		"56clicks.com",
		"56hj.cn",
		"56.js.cn",
		"5780.com",
		"57dy8.com",
		"5808l.com",
		"5850777.ru",
		"58611.net",
		"58tpw.com",
		"58.wf",
		"5a8www.peoplepaxy.com",
		"5-g.cn",
		"5thfinger.com",
		"5uyisheng.com",
		"5xian8.com",
		"6002288.com",
		"600z.com",
		"612100.cn",
		"616book.com",
		"618199.com",
		"61gamei.com",
		"62692222.com",
		"63810.com",
		"654v.com",
		"663998.net",
		"66600619.com",
		"6666mn.com",
		"6666p.com",
		"66av.cc",
		"66eexx.com",
		"66ml.in",
		"67www.com",
		"681luanlun.com",
		"685.so",
		"688ooo.com",
		"68fa.net",
		"6eeu.com",
		"71sise.com",
		"7.1tb.in",
		"71zijilu.com",
		"720movies.net",
		"75ww.com",
		"777mnz.com",
		"777partner.com",
		"777seo.com",
		"777txt.com",
		"7798991.com",
		"77tracking.com",
		"77zxzx.com",
		"78111.com",
		"78302.com",
		"7bpeople.com",
		"7dyw.com",
		"7pay.net",
		"7search.com",
		"7speed.info",
		"805678.com",
		"80887.com",
		"81182479.com",
		"818tl.com",
		"82sz.com",
		"84206.com",
		"85102152.com",
		"85kq.com",
		"863973.com",
		"888238.com",
		"8883448.com",
		"8885ff.com",
		"888758.com",
		"888888kk.com",
		"88bocai.net",
		"88kkvv.com",
		"8910ad.com",
		"8cbd.com",
		"8pyy.com",
		"900jpg.com",
		"900tif.com",
		"90888.com",
		"90900.com",
		"90tif.com",
		"911718.net",
		"924xx.com",
		"9523cc.com",
		"95kd.com",
		"9779.info",
		"978qp.com",
		"97boss.com",
		"97zb.com",
		"980media.com",
		"981718.cn",
		"99bthgc.me",
		"99count.com",
		"99eexx.com",
		"99kkxx.com",
		"99lwt.cn",
		"99meikang.com",
		"99shuding.com",
		"99tif.com",
		"99ypu.com",
		"99zzkk.com",
		"9gpan.com",
		"9rbk.com",
		"a.0day.kiev.ua",
		"a2132959.0lx.net",
		"a32.g.a.yimg.com",
		"a6a7.com",
		"a7mkp8m1ru.seojee.com",
		"a9.com",
		"aaa520.izlinix.com",
		"aaa.77xxmm.cn",
		"aaaxqabiqgxxwczrx.com",
		"aaddzz.com",
		"a-ads.com",
		"a.aproductmsg.com",
		"aarki.com",
		"aaron.fansju.com",
		"aa.xqwqbg.com",
		"abacho.net",
		"abbyspanties.com",
		"abc-ads.com",
		"abcmlm.com",
		"abcommunication.it",
		"abond.net",
		"abpressclub.com",
		"abris.montreapp.com",
		"absoluteclickscom.com",
		"abz.com",
		"academiebooks.org",
		"accessinvestment.net",
		"accounts.pkr.com.invalid",
		"accurate.gutterhalment.com",
		"acd.com.vn",
		"acento.com",
		"a.collective-media.net",
		"a.consumer.net",
		"a-counter.kiev.ua",
		"ac.rnm.ca",
		"acsseo.com",
		"actionsplash.com",
		"actionstudioworks.com",
		"activemeter.com",
		"actualdeals.com",
		"acuityads.com",
		"acusticjjw.pl",
		"ad01.mediacorpsingapore.com",
		"ad0.bigmir.net",
		"ad.100.tbn.ru",
		"ad.103092804.com",
		"ad1.emediate.dk",
		"ad1.emule-project.org",
		"ad1.kde.cz",
		"ad1.pamedia.com.au",
		"ad2flash.com",
		"ad2games.com",
		"ad2.iinfo.cz",
		"ad2.ip.ro",
		"ad2.linxcz.cz",
		"ad2.lupa.cz",
		"ad3.iinfo.cz",
		"ad3.pamedia.com.au",
		"ad4game.com",
		"ad.71i.de",
		"ad.980x.com",
		"ad.a8.net",
		"ad.abcnews.com",
		"ad.abctv.com",
		"ad.about.com",
		"ad.aboutit.de",
		"ad.aboutwebservices.com",
		"ad.abum.com",
		"adaction.de",
		"adadvisor.net",
		"ad.afy11.net",
		"ad.allstar.cz",
		"ad.altervista.org",
		"ad.amgdgt.com",
		"adanku.com",
		"ad.anuntis.com",
		"adapt.tv",
		"adap.tv",
		"ad.auditude.com",
		"ad-balancer.at",
		"ad-balancer.net",
		"adbanner.ro",
		"adbard.net",
		"ad.bizo.com",
		"adblade.com",
		"adblockanalytics.com",
		"ad.bnmla.com",
		"ad.bondage.com",
		"adboost.de.vu",
		"adboost.net",
		"adbooth.net",
		"adbot.com",
		"adbrite.com",
		"adbroker.de",
		"adbunker.com",
		"adbutler.com",
		"adbutler.de",
		"adbuyer3.lycos.com",
		"adbuyer.com",
		"ad.caradisiac.com",
		"adcash.com",
		"adcast.deviantart.com",
		"adcell.de",
		"adcel.vrvm.com",
		"ad-center.com",
		"adcenter.mdf.se",
		"adcenter.net",
		"adcentriconline.com",
		"ad.centrum.cz",
		"adcept.net",
		"ad.cgi.cz",
		"ad-check.disconnect.me",
		"ad.choiceradio.com",
		"adcito.com",
		"adclick.com",
		"adclient1.tucows.com",
		"adclient.uimserv.net",
		"adclix.org",
		"ad.clix.pt",
		"adcloud.net",
		"adcolony.com",
		"adcomplete.com",
		"adconion.com",
		"adcontent.gamespy.com",
		"ad.cooks.com",
		"ad.crwdcntrl.net",
		"adcycle.com",
		"addash.co",
		"addealing.com",
		"addesktop.com",
		"addfreestats.com",
		"ad.digitallook.com",
		"ad.directrev.com",
		"addme.com",
		"add.newmedia.cz",
		"ad.doctissimo.fr",
		"ad.domainfactory.de",
		"adecn.com",
		"ad.e-kolay.net",
		"ademails.com",
		"adengage.com",
		"ad.eurosport.com",
		"adexpose.com",
		"adext.inkclub.com",
		"ad.f1cd.ru",
		"adfactor.nl",
		"adfarm.mediaplex.com",
		"adflight.com",
		"ad.flurry.com",
		"adf.ly",
		"adforce.com",
		"adform.com",
		"ad.foxnetworks.com",
		"ad.freecity.de",
		"adfrut.cl",
		"adgardener.com",
		"ad.gate24.ch",
		"ad.globe7.com",
		"adgoto.com",
		"ad.grafika.cz",
		"adgridwork.com",
		"adgroups.net",
		"ad.hbv.de",
		"adheb.com",
		"adhese.be",
		"adhese.com",
		"ad.hodomobile.com",
		"ad.httpool.com",
		"ad.hyena.cz",
		"ad.iinfo.cz",
		"ad.ilove.ch",
		"adimage.asiaone.com.sg",
		"adimage.guardian.co.uk",
		"adimages.been.com",
		"adimages.carsoup.com",
		"adimages.go.com",
		"adimages.homestore.com",
		"adimages.omroepzeeland.nl",
		"adimages.sanomawsoy.fi",
		"ad-images.suntimes.com",
		"adi.mainichi.co.jp",
		"adimg1.chosun.com",
		"adimg.cnet.com",
		"adimg.com.com",
		"adimgs.sapo.pt",
		"adimg.uimserv.net",
		"adimpact.com",
		"adinch.com",
		"ad.infoseek.com",
		"adinjector.net",
		"adinterax.com",
		"adisfy.com",
		"adition.com",
		"adition.de",
		"adition.net",
		"adizio.com",
		"ad.jamba.net",
		"ad.jamster.co.uk",
		"ad.jetsoftware.com",
		"adjix.com",
		"adjug.com",
		"adjuggler.com",
		"adjuggler.yourdictionary.com",
		"adjust.io",
		"adjustnetwork.com",
		"adk2ads.tictacti.com",
		"adk2.com",
		"ad.keenspace.com",
		"adland.ru",
		"adlantic.nl",
		"ad.leadbolt.net",
		"adledge.com",
		"adlegend.com",
		"adlerobservatory.com",
		"adlink.de",
		"ad.liveinternet.ru",
		"adlog.com.com",
		"adloox.com",
		"adlooxtracking.com",
		"ad.lupa.cz",
		"adlure.net",
		"ad.m5prod.net",
		"admagnet1.com",
		"admagnet.net",
		"admailtiser.com",
		"admanagement.ch",
		"admanager.btopenworld.com",
		"admanager.carsoup.com",
		"adman.gr",
		"adman.in.gr",
		"adman.otenet.gr",
		"admarketplace.com",
		"admarketplace.net",
		"admarvel.com",
		"admarvel.s3.amazonaws.com",
		"admax.nexage.com",
		"admedia.com",
		"admedia.ro",
		"ad.media-servers.net",
		"ad.mediastorm.hu",
		"admedo.com",
		"admeld.com",
		"admerize.be",
		"admeta.com",
		"admex.com",
		"ad.mgd.de",
		"adminder.com",
		"adminshop.com",
		"admisoft.com",
		"admized.com",
		"admlaw.cn",
		"admob.com",
		"admob.comadwhirl.com",
		"admobile.com",
		"admon.cn",
		"admonitor.com",
		"admotion.com.ar",
		"admtpmp123.com",
		"admtpmp124.com",
		"ad.musicmatch.com",
		"ad.nachtagenten.de",
		"adnection.com",
		"adnet.asahi.com",
		"adnet.biz",
		"adnet.de",
		"adnetinteractive.com",
		"adnet-media.net",
		"adnet.ru",
		"adnetwork.net",
		"adnetworkperformance.com",
		"adnet.worldreviewer.com",
		"adnews.maddog2000.de",
		"adnotch.com",
		"ad.nozonedata.com",
		"ad.nttnavi.co.jp",
		"ad.nwt.cz",
		"adnxs.com",
		"adobe-update.com",
		"adocean.pl",
		"ad.onad.eu",
		"adongcomic.com",
		"adonspot.com",
		"adoperator.com",
		"adoreclothing.co.uk",
		"adorigin.com",
		"adpacks.com",
		"ad.pandora.tv",
		"ad-pay.de",
		"adpepper.dk",
		"adpepper.nl",
		"adperium.com",
		"adpia.vn",
		"ad.playground.ru",
		"adplus.co.id",
		"adplxmd.com",
		"ad.preferances.com",
		"adprimemedia.com",
		"adprofile.net",
		"ad.profiwin.de",
		"adprojekt.pl",
		"ad.prv.pl",
		"adq.nextag.com",
		"ad.rambler.ru",
		"adrazzi.com",
		"adreactor.com",
		"adremedy.com",
		"adreporting.com",
		"adres.internet.com",
		"ad.reunion.com",
		"adrevolver.com",
		"adriver.ru",
		"adrolays.de",
		"adrotate.de",
		"ad-rotator.com",
		"adrotator.se",
		"ads03.redtube.com",
		"ads10.speedbit.com",
		"ads180.com",
		"ads1.canoe.ca",
		"ads1.mediacapital.pt",
		"ads1.msn.com",
		"ads1.rne.com",
		"ads1.theglobeandmail.com",
		"ads1.virtual-nights.com",
		"ads2004.treiberupdate.de",
		"ads2.brazzers.com",
		"ads2.clearchannel.com",
		"ads2.contentabc.com",
		"ads2.gamecity.net",
		"ads2.jubii.dk",
		"ads2.net-communities.co.uk",
		"ads2.oneplace.com",
		"ads2.rne.com",
		"ads2.virtual-nights.com",
		"ads2.xnet.cz",
		"ads3.contentabc.com",
		"ads3.gamecity.net",
		"ads3.virtual-nights.com",
		"ads4.clearchannel.com",
		"ads4.gamecity.net",
		"ads4homes.com",
		"ads.4tube.com",
		"ads4.virtual-nights.com",
		"ads5.canoe.ca",
		"ads.5ci.lt",
		"ads5.virtual-nights.com",
		"ads6.gamecity.net",
		"ads7.gamecity.net",
		"ads8.com",
		"ads.abovetopsecret.com",
		"ads.aceweb.net",
		"ads.activestate.com",
		"ads.adfox.ru",
		"ads.administrator.de",
		"ads.adshareware.net",
		"ads.adultfriendfinder.com",
		"ads.adultswim.com",
		"ads.advance.net",
		"ads.adverline.com",
		"ads.affiliates.match.com",
		"ads.ak.facebook.com.edgesuite.net",
		"ads.allvatar.com",
		"ads.alt.com",
		"ads.alwayson-network.com",
		"ads.amdmb.com",
		"ads.amigos.com",
		"ads.aol.com",
		"ads.aol.co.uk",
		"ads.apn.co.nz",
		"ads.appsgeyser.com",
		"ads.as4x.tmcs.net",
		"ads.as4x.tmcs.ticketmaster.com",
		"ads.asia1.com.sg",
		"ads.asiafriendfinder.com",
		"ads.ask.com",
		"ads.aspalliance.com",
		"Adsatt.ABCNews.starwave.com",
		"adsatt.abc.starwave.com",
		"adsatt.espn.go.com",
		"adsatt.espn.starwave.com",
		"Adsatt.go.starwave.com",
		"ads.avazu.net",
		"ads.batpmturner.com",
		"ads.beenetworks.net",
		"ads.belointeractive.com",
		"ads.berlinonline.de",
		"ads.betanews.com",
		"ads.betfair.com",
		"ads.betfair.com.au",
		"ads.bigchurch.com",
		"ads.bigfoot.com",
		"ads.billiton.de",
		"ads.bing.com",
		"ads.bittorrent.com",
		"ads.blog.com",
		"ads.bloomberg.com",
		"ads.bluelithium.com",
		"ads.bluemountain.com",
		"ads.bluesq.com",
		"ads.bonniercorp.com",
		"ads.boylesports.com",
		"ads.brabys.com",
		"ads.brain.pk",
		"ads.brazzers.com",
		"ads.bumq.com",
		"ads.businessweek.com",
		"adsby.bidtheatre.com",
		"adscale.de",
		"ads.canalblog.com",
		"ad.scanmedios.com",
		"ads.canoe.ca",
		"ads.casinocity.com",
		"ads.cbc.ca",
		"ads.cc",
		"ads.cc-dt.com",
		"ads.cdn.rovio.com",
		"ads.centraliprom.com",
		"ads.cgnetworks.com",
		"ads.channel4.com",
		"adscholar.com",
		"adscience.nl",
		"ads.cimedia.com",
		"ads.clearchannel.com",
		"ads-click.com",
		"ads.co.com",
		"ads.com.com",
		"ads.contactmusic.com",
		"ads.contentabc.com",
		"ads.contextweb.com",
		"adscpm.com",
		"ads.crakmedia.com",
		"ads.creativematch.com",
		"ads.creative-serving.com",
		"ads.cricbuzz.com",
		"ads.cybersales.cz",
		"ads.dada.it",
		"adsdaq.com",
		"ads.datinggold.com",
		"ads.datingyes.com",
		"ads.dazoot.ro",
		"ads.deltha.hu",
		"ads.dennisnet.co.uk",
		"ads.desmoinesregister.com",
		"ads.detelefoongids.nl",
		"ads.deviantart.com",
		"ads.digital-digest.com",
		"ads.digitalmedianet.com",
		"ads.digitalpoint.com",
		"ads.directionsmag.com",
		"ads.discovery.com",
		"adsdk.com",
		"ads.domeus.com",
		"ads.eagletribune.com",
		"ads.easy-forex.com",
		"ads.eatinparis.com",
		"ads.economist.com",
		"ads.edbindex.dk",
		"ads.egrana.com.br",
		"ads.einmedia.com",
		"ads.electrocelt.com",
		"ads.elitetrader.com",
		"ads.emirates.net.ae",
		"adsend.de",
		"ad.sensismediasmart.com.au",
		"ads.epltalk.com",
		"adserve.ams.rhythmxchange.com",
		"adserver01.de",
		"adserver1.backbeatmedia.com",
		"adserver1-images.backbeatmedia.com",
		"adserver1.mindshare.de",
		"adserver1.mokono.com",
		"adserver1.ogilvy-interactive.de",
		"adserver2.mindshare.de",
		"adserver2.popdata.de",
		"adserver.43plc.com",
		"adserver.71i.de",
		"adserver.ads.com.ph",
		"adserver.adultfriendfinder.com",
		"adserver.aidameter.com",
		"adserver.aol.fr",
		"adserver.barrapunto.com",
		"adserver.beggarspromo.com",
		"adserver.betandwin.de",
		"adserver.bing.com",
		"adserver.bizhat.com",
		"adserver.break-even.it",
		"adserver.cams.com",
		"adserver.clashmusic.com",
		"adserver.com",
		"adserver.digitoday.com",
		"adserver.dotcommedia.de",
		"adserver.finditquick.com",
		"adserver.flossiemediagroup.com",
		"adserver.freecity.de",
		"adserver.freenet.de",
		"adserver.friendfinder.com",
		"ad-server.gulasidorna.se",
		"adserver.hardsextube.com",
		"adserver.hardwareanalysis.com",
		"adserver.html.it",
		"adserver.irishwebmasterforum.com",
		"adserver.janes.com",
		"adserver.kyoceramita-europe.com",
		"adserver.libero.it",
		"adserver-live.yoc.mobi",
		"adserver.motorpresse.de",
		"adserver.news.com.au",
		"adserver.ngz-network.de",
		"adserver.nydailynews.com",
		"adserver.o2.pl",
		"adserver.oddschecker.com",
		"adserver.omroepzeeland.nl",
		"ad-serverparc.nl",
		"adserver.pl",
		"adserverplus.com",
		"adserver.portalofevil.com",
		"adserver.portugalmail.net",
		"adserver.portugalmail.pt",
		"adserver.quizdingo.com",
		"adserver.realhomesex.net",
		"adserver.sanomawsoy.fi",
		"adserver.sciflicks.com",
		"adserver.sharewareonline.com",
		"adserversolutions.com",
		"adserver.spankaway.com",
		"adserver.startnow.com",
		"adserver.theonering.net",
		"adserver.twitpic.com",
		"adserver.viagogo.com",
		"adserver.virginmedia.com",
		"adserver.yahoo.com",
		"adserv.evo-x.de",
		"adserv.gamezone.de",
		"adserv.iafrica.com",
		"adservinginternational.com",
		"adserv.qconline.com",
		"adserv.quality-channel.de",
		"ads.esmas.com",
		"ads.eu.msn.com",
		"ads.exactdrive.com",
		"ads.expat-blog.biz",
		"ads.expedia.com",
		"ads.ezboard.com",
		"ad.seznam.cz",
		"adsfac.eu",
		"adsfac.net",
		"ads.factorymedia.com",
		"adsfac.us",
		"ads.fairfax.com.au",
		"ads.faxo.com",
		"ads.ferianc.com",
		"ads.filmup.com",
		"ads.financialcontent.com",
		"ads.flooble.com",
		"ads.fool.com",
		"ads.footymad.net",
		"ads.forbes.com",
		"ads.forbes.net",
		"ads.forium.de",
		"ads.fortunecity.com",
		"ads.fotosidan.se",
		"ads.foxkidseurope.net",
		"ads.foxnetworks.com",
		"ads.foxnews.com",
		"ads.freecity.de",
		"ads.friendfinder.com",
		"ads.ft.com",
		"ads.futurenet.com",
		"ads.gamecity.net",
		"ads.gameforgeads.de",
		"ads.gamershell.com",
		"ads.gamespyid.com",
		"ads.gamigo.de",
		"ads.gaming-universe.de",
		"ads.gawker.com",
		"ads.geekswithblogs.net",
		"ads.glispa.com",
		"ads.globeandmail.com",
		"ads.gmodules.com",
		"ads.godlikeproductions.com",
		"ads.goyk.com",
		"ads.gplusmedia.com",
		"ads.gradfinder.com",
		"ads.grindinggears.com",
		"ads.groundspeak.com",
		"ads.gsm-exchange.com",
		"ads.gsmexchange.com",
		"ads.guardian.co.uk",
		"ads.guardianunlimited.co.uk",
		"ads.guru3d.com",
		"ads.hardwaresecrets.com",
		"ads.harpers.org",
		"ads.hbv.de",
		"ads.hearstmags.com",
		"ads.heartlight.org",
		"ads.heias.com",
		"ads.hideyourarms.com",
		"ads.hollywood.com",
		"ads.horsehero.com",
		"ads.horyzon-media.com",
		"adshost1.com",
		"ads.iafrica.com",
		"ads.ibest.com.br",
		"ads.ibryte.com",
		"ads.icq.com",
		"adside.com",
		"ads.ign.com",
		"ad.simgames.net",
		"ads.img.co.za",
		"ads.imgur.com",
		"ads.indiatimes.com",
		"ads.infi.net",
		"ads.internic.co.il",
		"ads.ipowerweb.com",
		"ads.isoftmarketing.com",
		"ads.itv.com",
		"ads.iwon.com",
		"ads.jewishfriendfinder.com",
		"ads.jiwire.com",
		"ads.jobsite.co.uk",
		"ads.jpost.com",
		"ads.jubii.dk",
		"ads.justhungry.com",
		"adsk2.co",
		"ads.kaktuz.net",
		"adskape.ru",
		"ads.kelbymediagroup.com",
		"ads.kinobox.cz",
		"ads.kinxxx.com",
		"adsklick.de",
		"ads.kompass.com",
		"ads.krawall.de",
		"ads.lesbianpersonals.com",
		"ads.linuxfoundation.org",
		"ads.linuxjournal.com",
		"ads.linuxsecurity.com",
		"ads.livenation.com",
		"ad.slutload.com",
		"ads.mail3x.com",
		"ads.mariuana.it",
		"adsmarket.com",
		"ad.smartclip.net",
		"adsmart.com",
		"adsmart.co.uk",
		"adsmart.net",
		"ads.massinfra.nl",
		"ads.mcafee.com",
		"ads.mdotm.com",
		"ads.mediaodyssey.com",
		"ads.mediaturf.net",
		"ads.medienhaus.de",
		"ads.mgnetwork.com",
		"ads.mmania.com",
		"adsmobi.com",
		"ads.moceanads.com",
		"adsmogo.com",
		"ads.motor-forum.nl",
		"ads.motormedia.nl",
		"ads.movieflix.com",
		"ads.msn.com",
		"ads.multimania.lycos.fr",
		"ads.nationalgeographic.com",
		"adsnative.com",
		"ads.ncm.com",
		"ads.netclusive.de",
		"ads.netmechanic.com",
		"ads.networksolutions.com",
		"ads.newdream.net",
		"ads.newgrounds.com",
		"ads.newmedia.cz",
		"ads.newsint.co.uk",
		"ads.newsquest.co.uk",
		"ads.newtention.net",
		"ads.ninemsn.com.au",
		"ads.nj.com",
		"ads.nola.com",
		"ads.nordichardware.com",
		"ads.nordichardware.se",
		"ads.nwsource.com",
		"ads.nyi.net",
		"ads.nytimes.com",
		"ads.nyx.cz",
		"ads.nzcity.co.nz",
		"ads.o2.pl",
		"ads.oddschecker.com",
		"adsoftware.com",
		"ads.okcimg.com",
		"adsoldier.com",
		"ads.ole.com",
		"ads.olivebrandresponse.com",
		"adsolutions.yp.com",
		"adsonar.com",
		"ads.oneplace.com",
		"ads.ookla.com",
		"ads.optusnet.com.au",
		"ad-souk.com",
		"ads.outpersonals.com",
		"ads.p161.net",
		"ad-space.net",
		"adspace.ro",
		"ads.passion.com",
		"adspeed.net",
		"ads.pennet.com",
		"ads.penny-arcade.com",
		"ads.pheedo.com",
		"ads.phpclasses.org",
		"ads.pickmeup-ltd.com",
		"adspirit.de",
		"ads.pkr.com",
		"ads.planet.nl",
		"ads.pni.com",
		"ads.pof.com",
		"adsponse.de",
		"ads.powweb.com",
		"ads.primissima.it",
		"ads.printscr.com",
		"ads.prisacom.com",
		"ads.program3.com",
		"ads.psd2html.com",
		"ads.pushplay.com",
		"ads.quoka.de",
		"ads.rcs.it",
		"ads.recoletos.es",
		"ads.rediff.com",
		"ads.redlightcenter.com",
		"ads.redtube.com",
		"adsremote.scrippsnetworks.com",
		"ads.resoom.de",
		"ads.returnpath.net",
		"adsrevenue.net",
		"ads.rottentomatoes.com",
		"ads.rpgdot.com",
		"adsrv.deviantart.com",
		"adsrv.eacdn.com",
		"adsrv.iol.co.za",
		"adsrvr.org",
		"ads.s3.sitepoint.com",
		"ads.satyamonline.com",
		"ads.savannahnow.com",
		"ads.saymedia.com",
		"ads.scifi.com",
		"ads.seniorfriendfinder.com",
		"ads.sexinyourcity.com",
		"ads.shizmoo.com",
		"ads.shopstyle.com",
		"ads.sift.co.uk",
		"ads.silverdisc.co.uk",
		"ads.slim.com",
		"ads.smartclick.com",
		"ads.soft32.com",
		"ads.space.com",
		"ads.spoonfeduk.com",
		"ads.sptimes.com",
		"ads.stackoverflow.com",
		"adsstat.com",
		"ads.stationplay.com",
		"ads.struq.com",
		"ads.sun.com",
		"ads.supplyframe.com",
		"ads.tahono.com",
		"adstat.4u.pl",
		"ads.techtv.com",
		"ads.techweb.com",
		"ads.telegraph.co.uk",
		"adstest.weather.com",
		"ads.theglobeandmail.com",
		"ads.themovienation.com",
		"ads.thestar.com",
		"ads.thewebfreaks.com",
		"ads.timeout.com",
		"ads.tjwi.info",
		"ads.tmcs.net",
		"ads.t-online.de",
		"ads.totallyfreestuff.com",
		"ads.townhall.com",
		"ads.trinitymirror.co.uk",
		"ads.tripod.com",
		"ads.tripod.lycos.co.uk",
		"ads.tripod.lycos.de",
		"ads.tripod.lycos.es",
		"ads.tripod.lycos.it",
		"ads.tripod.lycos.nl",
		"ads.tripod.spray.se",
		"ads.tso.dennisnet.co.uk",
		"ads.uknetguide.co.uk",
		"ads.ultimate-guitar.com",
		"ads.uncrate.com",
		"ads.undertone.com",
		"adsupplyads.com",
		"adsupply.com",
		"ads.usatoday.com",
		"ads.v3.com",
		"ads.verticalresponse.com",
		"ads.vgchartz.com",
		"ads.videosz.com",
		"ads.virtualcountries.com",
		"ads.virtual-nights.com",
		"ads.vnumedia.com",
		"ads.waps.cn",
		"ads.wapx.cn",
		"ads.weather.ca",
		"ads.web.aol.com",
		"ads.web.cs.com",
		"ads.web.de",
		"ads.webmasterpoint.org",
		"ads.websiteservices.com",
		"ads.whi.co.nz",
		"ads.whoishostingthis.com",
		"ads.wiezoekje.nl",
		"ads.wikia.nocookie.net",
		"ads.wineenthusiast.com",
		"adswitcher.com",
		"ads.wunderground.com",
		"ads.wwe.biz",
		"ads.xhamster.com",
		"ads.xtra.co.nz",
		"ads.y-0.net",
		"ads.yimg.com",
		"ads.yldmgrimg.net",
		"adsymptotic.com",
		"adsynergy.com",
		"ads.yourfreedvds.com",
		"ads.youtube.com",
		"adsystem.simplemachines.org",
		"adsys.townnews.com",
		"ads.zdnet.com",
		"ads.ztod.com",
		"ad.tbn.ru",
		"ad-tech.com",
		"adtech.com",
		"adtech.de",
		"ad.technoratimedia.com",
		"adtechus.com",
		"adtegrity.net",
		"adtheorent.com",
		"ad.thewheelof.com",
		"adthis.com",
		"adtiger.de",
		"adtilt.com",
		"adtoll.com",
		"adtology.com",
		"adtoma.com",
		"ad.top50.to",
		"adtrace.org",
		"adtrade.net",
		"adtrading.de",
		"adtrak.net",
		"adtriplex.com",
		"adtruth.com",
		"ad.turn.com",
		"ad.tv2.no",
		"ad.twitchguru.com",
		"adultadvertising.com",
		"adultfreevideos.net",
		"adultmoda.com",
		"ad-up.com",
		"ad.usatoday.com",
		"advabnr.com",
		"adv-adserver.com",
		"advanceworks.cn",
		"advariant.com",
		"adv-banner.libero.it",
		"adv.cooperhosting.net",
		"adventory.com",
		"advert.bayarea.com",
		"advert.dyna.ultraweb.hu",
		"adverticum.com",
		"adverticum.net",
		"adverticus.de",
		"advertise.com",
		"advertiseireland.com",
		"advertisespace.com",
		"advertising.aol.com",
		"advertising.apple.com",
		"advertisingbanners.com",
		"advertisingbox.com",
		"advertising.com",
		"advertising.guildlaunch.net",
		"advertising.microsoft.com",
		"advertising.yahoo.com",
		"advertmarket.com",
		"advertmedia.de",
		"advertpro.sitepoint.com",
		"advertpro.ya.com",
		"adverts.carltononline.com",
		"advertserve.com",
		"advertstream.com",
		"advertwizard.com",
		"adv.freeonline.it",
		"adv.hwupgrade.it",
		"advideo.uimserv.net",
		"adview.ppro.de",
		"adv-inc-net.com",
		"ad.virtual-nights.com",
		"advisormedia.cz",
		"adviva.com",
		"adviva.net",
		"adv.livedoor.com",
		"advnt.com",
		"adv.webmd.com",
		"adv.wp.pl",
		"adv.yo.cz",
		"adware-guard.com",
		"adwareremovergold.com",
		"ad.watch.impress.co.jp",
		"ad.wavu.hu",
		"ad.way.cz",
		"ad.weatherbug.com",
		"adwhirl.com",
		"adwitserver.com",
		"adworldnetwork.com",
		"adworx.at",
		"adworx.be",
		"adworx.nl",
		"ad.wsod.com",
		"ad.wz.cz",
		"adx.allstar.cz",
		"adx.atnext.com",
		"adx.gainesvillesun.com",
		"adxpansion.com",
		"adxpose.com",
		"adxvalue.com",
		"ad.yadro.ru",
		"adyea.com",
		"ad.yourmedia.com",
		"ad.zanox.com",
		"adzerk.net",
		"adzerk.s3.amazonaws.com",
		"adzones.com",
		"aeaer.com",
		"aeysop.com",
		"af-ad.co.uk",
		"af-cn.com",
		"afering.com",
		"affbuzzads.com",
		"affiliate.1800flowers.com",
		"affiliate.7host.com",
		"affiliate.doubleyourdating.com",
		"affiliate.dtiserv.com",
		"affiliatefuel.com",
		"affiliatefuture.com",
		"affiliate.gamestop.com",
		"affiliate.mercola.com",
		"affiliate.mogs.com",
		"affiliate.offgamers.com",
		"affiliates.allposters.com",
		"affiliates.babylon.com",
		"affiliates.devilfishpartners.com",
		"affiliates.digitalriver.com",
		"affiliates.globat.com",
		"affiliates.ige.com",
		"affiliates.internationaljock.com",
		"affiliates.jlist.com",
		"affiliates.streamray.com",
		"affiliates.thinkhost.net",
		"affiliates.thrixxx.com",
		"affiliates.ultrahosting.com",
		"affiliatetracking.com",
		"affiliatetracking.net",
		"affiliatetrading.net",
		"affiliate.travelnow.com",
		"affiliate.viator.com",
		"affiliatewindow.com",
		"affiliation-france.com",
		"affili.net",
		"afftracking.justanswer.com",
		"afsoft.de",
		"afterlabs.com",
		"agency.thinkalee.ca",
		"agroluftbild.de",
		"agronutrientes.com.mx",
		"agwoan.com",
		"ahalogy.com",
		"ahbddp.com",
		"ahczwz.com",
		"ahdqja.com",
		"ah-ha.com",
		"ahhpjj.com",
		"ahjhsl.com",
		"ahlswh.net",
		"ahlxwh.com",
		"ahmhls.com",
		"ahwydljt.com",
		"ahxldgy.com",
		"ahzhaosheng.com.cn",
		"ahzh-pv.com",
		"ahzxy.com",
		"aidu-ads.de",
		"aigunet.com",
		"aileronx.com",
		"ailvgo.com",
		"aim4media.com",
		"aipp-italia.it",
		"airbrake.io",
		"airpush.com",
		"airtyrant.com",
		"aistat.net",
		"aiwoxin.com",
		"ajarixusuqux.com",
		"ajouter.net",
		"ajusa.net",
		"ajzl8090.com",
		"akdanji.yxdown.cn",
		"akissoo.com",
		"akorenramizefendiyurdu.com",
		"akshatadesigns.in",
		"aktrack.pubmatic.com",
		"alchenomy.com",
		"alclick.com",
		"alcochemphil.com",
		"alcoenterprises.com",
		"alecctv.com",
		"aleksandr-usov.com",
		"alemeitu.com",
		"alenty.com",
		"alex2006.friko.pl",
		"alexa-sitestats.s3.amazonaws.com",
		"ali59000.free.fr",
		"alishantea-tw.com",
		"all4spy.com",
		"all-about-you-sxm.com",
		"alladvantage.com",
		"allenwireline.com",
		"allluki.ru",
		"allosponsor.com",
		"allsmail.com",
		"allstarmediagroup.com",
		"alltraff.ru",
		"alphaprinthouse.org",
		"alphaxiom.com",
		"alruno.home.pl",
		"alsera.de",
		"altan5.com",
		"altzx.cn",
		"amazingcounters.com",
		"amazingunigrace.com",
		"amazon-adsystem.com",
		"ameim.com",
		"amerarani.com",
		"american-carpet.com.tr",
		"americantribute.org",
		"amino-cn.com",
		"a.mktw.net",
		"amo122.com",
		"amobee.com",
		"amskrupajal.org",
		"amung.us",
		"amusecity.com",
		"an4u.com",
		"anafartalartml.k12.tr",
		"anahtars.com",
		"analytics.adpost.org",
		"analytics.google.com",
		"analytics.live.com",
		"analytics.yahoo.com",
		"anamol.net",
		"anayaoeventos.com",
		"ancientroom.com",
		"andayiyuan.com",
		"andlu.org",
		"andreas-gehring.com",
		"andrewmelchior.com",
		"andreyzakharov.com",
		"android-guard.com",
		"andsto57cksstar.rr.nu",
		"angelangle.co.uk",
		"anhui-attorney.com",
		"anhuiguzhai.com",
		"anhuihongdapme.com",
		"anhui-rili.com",
		"animeonline.net",
		"anmeiqi.com",
		"anm.intelli-direct.com",
		"annengdl.com",
		"annonser.dagbladet.no",
		"a.nt002.cn",
		"an.tacoda.net",
		"ant.trenz.pl",
		"anzhongkj.com",
		"anzhuo6.com",
		"aolikes.com",
		"aonikesi.com",
		"aos1738.com",
		"apartment-mall.cn",
		"ap-design.com.ar",
		"aperomanagement.fr",
		"apex-ad.com",
		"apexlpi.com",
		"apextechnotools.com",
		"api.addthis.com",
		"api.intensifier.de",
		"apiparbion.com",
		"appads.com",
		"appboy.com",
		"appdog.com",
		"appflood.com",
		"apphay.me",
		"appia.com",
		"appier.com",
		"apple-es.com",
		"applovin.com",
		"appnexus.com",
		"appolicious.com",
		"appprices.com",
		"app-promo.com",
		"apprebates.com",
		"appredeem.com",
		"approstar.com",
		"appsdt.com",
		"app.seojee.com",
		"appsfire.com",
		"appsfire.net",
		"appsflyer.com",
		"appsnack.com",
		"apptera.com",
		"appular.com",
		"apsalar.com",
		"ap-transz.hu",
		"apture.com",
		"aqbly.com",
		"aquapuremultiservicios.es",
		"arabsanfrancisco.com",
		"arc1.msn.com",
		"arcadebanners.com",
		"architectchurch.com",
		"archtopmakers.com",
		"archwiadomosci.com",
		"ard.xxxblackbook.com",
		"arenamakina.com",
		"are-ter.com",
		"argentinaglobalwines.com",
		"argoauto.net",
		"arianfosterprobowljersey.com",
		"aricimpastanesi.com",
		"arizst.ru",
		"armadaneo.info",
		"armazones.com",
		"armstrongflooring.mobi",
		"arouersobesite.free.fr",
		"arprosports.com.ar",
		"arqxxg.com",
		"arthalo.com",
		"as1.advfn.com",
		"as2.advfn.com",
		"as5000.com",
		"a.sakh.com",
		"asbeirasporto.com",
		"asess.com.mx",
		"asfirey.com",
		"asiaok.net",
		"asilteknik.net",
		"asj999.com",
		"askdoctorz.com",
		"assainissement-btp-guadeloupe.com",
		"assets1.exgfnetwork.com",
		"assets.loomia.com",
		"assexyas.com",
		"assistantbilling.in",
		"assoc-amazon.com",
		"associazioneiltrovatore.it",
		"asstraffic18.net",
		"asthanabrothers.com",
		"as.webmd.com",
		"at-adserver.alltop.com",
		"atdmt.com",
		"ateresraffle.com",
		"athena-ads.wikia.com",
		"athomenetwork.hu",
		"atlassolutions.com",
		"atwola.com",
		"a.ucoz.net",
		"a.ucoz.ru",
		"auctionads.com",
		"auctionads.net",
		"auctionbowling.com",
		"audience2media.com",
		"audit.median.hu",
		"auditssmsf.com.au",
		"audit.webinform.hu",
		"augami.net",
		"aupvfp.com",
		"ausubelinstituto.edu.mx",
		"autcontrol.ir",
		"autizmus.n1.hu",
		"auto-bannertausch.de",
		"autohits.dk",
		"autosloansonlines.com",
		"av356.com",
		"av5k.com",
		"avenuea.com",
		"av.ghura.pl",
		"avpa.javalobby.org",
		"avres.net",
		"avsads.com",
		"avtobanka.ru",
		"avtobaraxlo.ru",
		"awempire.com",
		"awin1.com",
		"axa3.cn",
		"a.xanga.com",
		"axis-online.pl",
		"axjp.cn",
		"ayile.com",
		"aylarl.com",
		"azazaz.eu",
		"azfront.com",
		"azteou.com",
		"b-1st.com",
		"b4psads.com",
		"b9a.net",
		"ba.afl.rakuten.co.jp",
		"babao.twhl.net",
		"babs.tv2.dk",
		"baby.py.shangdu.com",
		"backbeatmedia.com",
		"badaonz.com",
		"bag86.com",
		"baichenge.com",
		"baidukd.com",
		"baiduyisheng.com",
		"baifa88.com",
		"baizun.bi2vl.com",
		"bakuzbuq.ru",
		"balochrise.com",
		"baloonwalkingpet.co.uk",
		"banana.automaxcenter.ro",
		"banati-bags.ru",
		"bango.combango.org",
		"bango.net",
		"banik.redigy.cz",
		"banner.ad.nu",
		"bannerads.de",
		"banner.alphacool.de",
		"banner.ambercoastcasino.com",
		"banner.blogranking.net",
		"bannerboxes.com",
		"banner.buempliz-online.ch",
		"banner.casinodelrio.com",
		"banner.casino.net",
		"bannercommunity.de",
		"bannerconnect.com",
		"bannerconnect.net",
		"banner.cotedazurpalace.com",
		"banner.coza.com",
		"banner.cz",
		"banner.easyspace.com",
		"banner.elisa.net",
		"banner.eurogrand.com",
		"banner-exchange-24.de",
		"bannerexchange.cjb.net",
		"banner.featuredusers.com",
		"bannerflow.com",
		"banner.getgo.de",
		"banner.goldenpalace.com",
		"bannergrabber.internet.gr",
		"bannerhost.com",
		"bannerimage.com",
		"banner.img.co.za",
		"banner.inyourpocket.com",
		"banner.jobsahead.com",
		"banner.joylandcasino.com",
		"banner.kiev.ua",
		"bannerlandia.com.ar",
		"banner.linux.se",
		"bannermall.com",
		"bannermarkt.nl",
		"banner.media-system.de",
		"banner.mindshare.de",
		"banner.nixnet.cz",
		"banner.noblepoker.com",
		"banner.northsky.com",
		"banner.orb.net",
		"banner.penguin.cz",
		"bannerpower.com",
		"banner.prestigecasino.com",
		"banner.rbc.ru",
		"banner.relcom.ru",
		"banner.ringofon.com",
		"banners.adultfriendfinder.com",
		"banners.amigos.com",
		"banners.apnuk.com",
		"banners.asiafriendfinder.com",
		"banners.audioholics.com",
		"banners.babylon-x.com",
		"banners.bol.com.br",
		"banners.cams.com",
		"banners.clubseventeen.com",
		"banners.czi.cz",
		"banners.dine.com",
		"banners.direction-x.com",
		"banners.directnic.com",
		"banners.easydns.com",
		"banners.ebay.com",
		"bannerserver.com",
		"banners.freett.com",
		"banners.friendfinder.com",
		"banners.getiton.com",
		"bannersgomlm.com",
		"bannershotlink.perfectgonzo.com",
		"banners.iq.pl",
		"banners.isoftmarketing.com",
		"banners.lifeserv.com",
		"banners.linkbuddies.com",
		"bannersng.yell.com",
		"bannerspace.com",
		"banners.passion.com",
		"banners.resultonline.com",
		"banners.sexsearch.com",
		"banners.sys-con.com",
		"banners.thomsonlocal.com",
		"banners.videosz.com",
		"banners.virtuagirlhd.com",
		"bannerswap.com",
		"banners.wunderground.com",
		"banner.tanto.de",
		"bannertesting.com",
		"banner.titan-dsl.de",
		"banner.vadian.net",
		"banner.webmersion.com",
		"banner.wirenode.com",
		"bannery.cz",
		"bannieres.acces-contenu.com",
		"bans.adserver.co.il",
		"bans.bride.ru",
		"bansuochina.com",
		"b.aol.com",
		"baolinyouxipingtai.com",
		"barbaros.com",
		"barnesandnoble.bfast.com",
		"barristers.ru",
		"bartnagel.tv",
		"baryote.com",
		"basic-check.disconnect.me",
		"bayansayfasi.com",
		"baypops.com",
		"bbelements.com",
		"bblogspot.com",
		"bbn.img.com.ua",
		"bbnp.com",
		"bbnwl.cn",
		"bbpama.com",
		"bbqdzx.com",
		"bbs.cndeaf.com",
		"bbs.hanndec.com",
		"bbs.jucheyoufu.com",
		"bbs.nxdushi.com",
		"bbs.tiens.net.cn",
		"bbs.zgfhl.com",
		"bcfads.com",
		"bc.kuaiche.com",
		"bcmediagroup.com",
		"beautyperfect.com.sg",
		"beautysane.ru",
		"becjiewedding.com",
		"beckerseguros.com.br",
		"begun.ru",
		"behave.nualias.com",
		"bei3.8910ad.com",
		"beidahuangheifeng.com",
		"beijingpifukeyiyuan.com",
		"beikehongbei.com",
		"beixue8018.com",
		"belstat.com",
		"belstat.nl",
		"b.engadget.com",
		"benghui.org",
		"benstock.free.fr",
		"benyuanbaina.com",
		"beroepsperformancescan.nl",
		"berp.com",
		"bestchefcafe.ro",
		"bestdarkstar.info",
		"bestfilesdownload.com",
		"bestload.in",
		"best-med-shop.com",
		"bestpons.net",
		"best-pr.info",
		"bestsearch.net",
		"best-top.ro",
		"besttru.qpoe.com",
		"bestway.cz",
		"bestyandex.com",
		"beta.spb0.ru",
		"bettercatch.com",
		"bga100.cn",
		"bgs.qhedu.net",
		"bhajankutir.vedicseasons.com",
		"bhclicks.com",
		"bh.lhdna.com",
		"bhpds.com",
		"bi2vl.com",
		"bianca.com.tr",
		"biawwer.com",
		"bibitupian.com",
		"bidclix.com",
		"bidclix.net",
		"bidswitch.net",
		"bidtrk.com",
		"bidvertiser.com",
		"bigads.guj.de",
		"bigbangmedia.com",
		"bigclicks.com",
		"biggeorge.com",
		"bigwis.com",
		"biiduh.com",
		"bikerouteshop.com",
		"billboard.cz",
		"bill.wiedemann.com",
		"bimlocal.com",
		"bioito.cn",
		"biolat.org",
		"bisimai.com",
		"bitads.net",
		"bitmedianetwork.com",
		"bivouac-iguana-sahara-merzouga.com",
		"bizad.nikkeibp.co.jp",
		"bizrate.com",
		"bjaimu.cn",
		"bjdenon.com",
		"bjdxhs.com",
		"bjdy123.com",
		"bj-fengshi.com",
		"bjhh998.com",
		"bjhmt.com",
		"bjhycd.net",
		"bjhzlr.com",
		"bjjmywcb.com",
		"bjmn100.com",
		"bjpgqsc.com",
		"bjtysj.cn",
		"bjxdzg.com",
		"bjzksj.com.cn",
		"bkkjob.com",
		"bkkwedding.com",
		"bkook.cn",
		"bkrtx.com",
		"b.l-a-c.cn",
		"blackfalcon3.net",
		"blackry.com",
		"blacksheepatlanta.com",
		"blacksoftworld.com",
		"blast4traffic.com",
		"bleachkon.net",
		"bliman.com",
		"blingbucks.com",
		"blog.3kingsclothing.com",
		"blogads.com",
		"blogatcomunica.com.br",
		"blogcounter.de",
		"blog.fm120.com",
		"blogherads.com",
		"blogrush.com",
		"blogtoplist.se",
		"blogtopsites.com",
		"blueadvertise.com",
		"bluecava.com",
		"blueendless.com",
		"bluekai.com",
		"bluelithium.com",
		"bluewhaleweb.com",
		"blushing.findgutterhelmet.com",
		"blutrumpet.com",
		"blwvcj.com",
		"bm.annonce.cz",
		"bn.bfast.com",
		"b.nt002.cn",
		"boersego-ads.de",
		"bogocn.com",
		"bohoth.com",
		"boldchat.com",
		"bolo100.com",
		"bomar-spa.com",
		"bonuswlf.bget.ru",
		"bookav.net",
		"bookmark.t2t2.com",
		"boomads.com",
		"boom.ro",
		"boost-my-pr.de",
		"boquan.net",
		"boramind.co.kr",
		"bor-bogdanych.com",
		"bordobank.net",
		"bori58.com",
		"bori82.com",
		"bormanns-wetter.de",
		"borun.org",
		"boryin.com",
		"boryin.net",
		"bos.cnusher.in",
		"bossmb.com",
		"bostelbekersv.com",
		"bothwellbridge.co.uk",
		"boutique-miniature.com",
		"bovusforum.com",
		"bowling.co.kr",
		"box.anchorfree.net",
		"boydfiber.com",
		"bpath.com",
		"bqbbw.com",
		"bradyhansen.com",
		"braincash.com",
		"brandmeacademy.com",
		"brandreachsys.com",
		"brandschutztechnik-hartmann.de",
		"branovate.com",
		"brave.ebod.co.uk",
		"bravenet.com.invalid",
		"brenz.pl",
		"brickandmobile.com",
		"bridgetrack.com",
		"brightinfo.com",
		"british-banners.com",
		"bronotak.cn",
		"bslukq.com",
		"bs.yandex.ru",
		"b.szwzcf.com",
		"btrll.com",
		"btwosfunny.onthenetas.com",
		"buchedosa.ye.ro",
		"budsinc.com",
		"bugsense.com",
		"buildingschool.net",
		"bullseye.backbeatmedia.com",
		"buo.cc",
		"burstly.com",
		"burstmedia.com",
		"busanprint.net",
		"business.opera.com",
		"buthoprus.narod.ru",
		"butikzabava.ru",
		"buyhitscheap.com",
		"buyonshop.com",
		"buysellads.com",
		"buzzonclick.com",
		"bvalphaserver.com",
		"bwegz.cn",
		"bwisa.org",
		"bwp.download.com",
		"bxpaffc.com",
		"bxzxw.net",
		"byrukk.com",
		"bytim.net",
		"c1.nowlinux.com",
		"c242k.com",
		"cabomarlinisportfishing.com",
		"cache.addthiscdn.com",
		"cadastrabb.com",
		"cadxiedan.com",
		"cafatc.com",
		"cafe-being.com",
		"caliresolutions.com",
		"callfire.com",
		"callloop.com",
		"camberfam.de",
		"cambouisfr.free.fr",
		"cameradongbac.com",
		"campaign.bharatmatrimony.com",
		"camservicesgroup.com",
		"canadabook.ca",
		"canadattparts.com",
		"cancerlove.org",
		"caniamedia.com",
		"carbonads.com",
		"carbonads.net",
		"carloselmago.com",
		"cars.constructionwitness.net",
		"casalemedia.com",
		"casalmedia.com",
		"cash4members.com",
		"cash4popup.de",
		"cashcrate.com",
		"cashengines.com",
		"cashfiesta.com",
		"cashlayer.com",
		"cashpartner.com",
		"casinogames.com",
		"casinopays.com",
		"casinorewards.com",
		"casinotraffic.com",
		"casinotreasure.com",
		"cat-breeds.net",
		"catherineminnis.com",
		"caturismo.com.ar",
		"cavaliersales.com",
		"caymanlandsales.com",
		"cbanners.virtuagirlhd.com",
		"cbcoffices.com",
		"cben1.net",
		"c.bigmir.net",
		"cbmall.com",
		"cbvccc.com",
		"cbx.net",
		"ccbyz.com",
		"ccduniv.com",
		"ccjbox.ivyro.net",
		"c.compete.com",
		"cctjly.com",
		"cctvec.com",
		"ccycny.com",
		"cdhomexpo.cn",
		"cdlitong.com",
		"cdmswj.com",
		"cdn.freefacti.com",
		"cdpns.com",
		"cdyb.net",
		"cecash.com",
		"celltick.com",
		"celtra.com",
		"centerpieces-with-feathers-for-weddi.blogspot.com",
		"centralamericarealestateinvestment.com",
		"centro-guzzi-bielefeld.de",
		"centro-moto-guzzi.de",
		"ceocms.com",
		"ceoxchange.cn",
		"cescon.ca",
		"ceskydomov.alias.ngs.modry.cz",
		"cetrk.com",
		"cfbrr.com",
		"cfcgl.com",
		"cfnmking.com",
		"cfwudao.cc",
		"cgicounter.puretec.de",
		"cgispy.com",
		"chairmarket.net",
		"chaling518.com",
		"chango.com",
		"channelintelligence.com",
		"chartbeat.com",
		"chartbeat.net",
		"chartboost.com",
		"chart.dk",
		"cheapness.byefelicia.fr",
		"checkm8.com",
		"checkstat.nl",
		"check-updates.net",
		"cheminfos.com",
		"chenmo.hrb600.com",
		"chenyulaser.com",
		"cheshirehockey.com",
		"chestionar.ro",
		"chhmc.com",
		"china012.com",
		"chinabestex.com",
		"chinabodagroup.com",
		"chinabosom.com",
		"chinacxyy.com",
		"china.c-zs.com",
		"chinafsw.cn",
		"china-hangyi.com",
		"china-jlt.com",
		"chinalve.com",
		"chinashadenet.com",
		"china-sxw.net",
		"chinatlz.com",
		"chinazehui.com",
		"china-zhenao.com",
		"chinese.ahzh-pv.com",
		"chinesevie.com",
		"chitika.com",
		"chitika.net",
		"chizhou360.cn",
		"chizhoubymy.com",
		"chlawhome.org",
		"choongmoosports.co.kr",
		"ch.questionmarket.com",
		"christianmensfellowshipsoftball.org",
		"chungcheng.net",
		"chunxiady.com",
		"chupiao365.com",
		"chura.pl",
		"cibleclick.com",
		"cibonline.org",
		"cinemaedvd.com",
		"citipups.net",
		"cityads.telus.net",
		"citygrid.com",
		"cjbmanagement.com",
		"cjcajf.com",
		"cj.com",
		"cjlog.com",
		"ckidkina.ru",
		"ckt4.cn",
		"clancommission.us",
		"claria.com",
		"clashmobile.com",
		"class-act-clicks.com",
		"click2freemoney.com",
		"click2paid.com",
		"click79.com",
		"clickability.com",
		"click.absoluteagency.com",
		"clickadz.com",
		"clickagents.com",
		"clickbank.com",
		"clickbank.net",
		"clickbooth.com",
		"clickboothlnk.com",
		"clickbrokers.com",
		"clickcompare.co.uk",
		"clickdensity.com",
		"clickedyclick.com",
		"click.fool.com",
		"clickhereforcellphones.com",
		"clickhouse.com",
		"clickhype.com",
		"click.kmindex.ru",
		"clicklink.jp",
		"clickmedia.ro",
		"clicks.equantum.com",
		"clickserve.cc-dt.com",
		"clicks.mods.de",
		"clicksor.com",
		"clicktag.de",
		"clickthrucash.com",
		"clickthruserver.com",
		"clickthrutraffic.com",
		"clicktrace.info",
		"clicktracks.com",
		"clicktrack.ziyu.net",
		"clicktrade.com",
		"clickxchange.com",
		"clickz.com",
		"clickzxc.com",
		"clicmanager.fr",
		"clients.tbo.com",
		"clixgalore.com",
		"clkads.com",
		"clk.mongxw.com",
		"clkrev.com",
		"clk.sjopt.com",
		"cls.vrvm.com",
		"clubfrontenisnaquera.es",
		"cluster.adultworld.com",
		"clustrmaps.com",
		"cmpstar.com",
		"cn81301.com",
		"cndownmb.com",
		"cneroc.com",
		"cnld.ru",
		"cn-lushan.com",
		"cnomy.com",
		"cnrdn.com",
		"cn-server.com",
		"cnt1.pocitadlo.cz",
		"cnt.spbland.ru",
		"cnvljo.com",
		"cnyongjiang.com",
		"co3corp.com",
		"co.at.vc",
		"code-server.biz",
		"coffee4u.pl",
		"coleccionperezsimon.com",
		"colonize.com",
		"com100com.com",
		"com300com.com",
		"comboapp.com",
		"comclick.com",
		"commindo-media-ressourcen.de",
		"commissioncrusher.com",
		"commissionmonster.com",
		"commitse.ru",
		"compactbanner.com",
		"company-target.com",
		"compdata.ca",
		"compiskra.ru",
		"comprabanner.it",
		"compsystech.com",
		"computerquestions.on.nimp.org",
		"concerone.com",
		"condosguru.com",
		"config.0551fs.com",
		"congchuzs.com",
		"connextra.com",
		"conservative.ru",
		"constructiveopinions.com",
		"consultdesk.com",
		"contaxe.de",
		"contentabc.com",
		"content.acc-hd.de",
		"content.ad",
		"contextweb.com",
		"conversantmedia.com",
		"conversionruler.com",
		"cookies.cmpnet.com",
		"cooper.mylftv.com",
		"copphangoccuong.com",
		"coremetrics.com",
		"coretalk.co",
		"corsa-cologne.de",
		"corsran.com",
		"count6.rbc.ru",
		"counted.com",
		"counter.avtoindex.com",
		"counter.bloke.com",
		"counter.cnw.cz",
		"counter.cz",
		"counter.dreamhost.com",
		"counter.fateback.com",
		"counter.mirohost.net",
		"counter.mojgorod.ru",
		"counter.nowlinux.com",
		"counter.rambler.ru",
		"counter.search.bg",
		"counters.honesty.com",
		"counter.sparklit.com",
		"counter.yadro.ru",
		"countinfo.com",
		"counting.kmindex.ru",
		"count.ly",
		"count.rbc.ru",
		"count.rin.ru",
		"counts.tucows.com",
		"count.west263.com",
		"coupling-media.de",
		"covenantoffire.com",
		"cowbears.nl",
		"cow.gutterheaters.org",
		"cpajump.centenr.com",
		"cpalead.com",
		"cpays.com",
		"cpi-istanbul.com",
		"cpmaffiliation.com",
		"cpmstar.com",
		"cpxadroit.com",
		"cpxinteractive.com",
		"cq6688.com",
		"cqcounter.com",
		"cqtspj.com",
		"crakmedia.com",
		"craktraffic.com",
		"crashlytics.com",
		"craveandlamb.com",
		"crawlability.com",
		"crazypopups.com",
		"creafi.com",
		"creafi-online-media.com",
		"creative.ak.facebook.com",
		"creatives.as4x.tmcs.net",
		"creatives.co.in",
		"creative-serving.com",
		"creatives.livejasmin.com",
		"creative.whi.co.nz",
		"creativitygap.com",
		"crfuwutai.com",
		"crispads.com",
		"crispmedia.com",
		"crispwireless.com",
		"criteo.com",
		"crittercism.com",
		"crossleather.com",
		"crow-dc.ru",
		"crowdgravity.com",
		"crtv.mate1.com",
		"crwdcntrl.net",
		"crxart.go.ro",
		"csbjkj.com",
		"csccabouco.com",
		"csdian.net",
		"ctnetwork.hu",
		"ctv.whpx8.com",
		"cubics.com",
		"cuboacores.com",
		"cugq.com",
		"cuhmqe.com",
		"cuijian.net",
		"curiouserdesserts.com",
		"customad.cnn.com",
		"custom-blacklisted-tracking-example.com",
		"cutheatergroup.cn",
		"cwettqtlffki.com",
		"cwipta.com",
		"cx81.com",
		"cxfd.net",
		"cxiozg.com",
		"cyberbounty.com",
		"cybermonitor.com",
		"cye-fscp.com",
		"cylm.jh56.cn",
		"cypgroup.com",
		"czbaoyu.com",
		"czgtgj.com",
		"czhjln.com",
		"czhyjz.com",
		"czqmc.com",
		"czwndl.com",
		"d24.0772it.net",
		"d.91soyo.com",
		"d99q.cn",
		"dacdac.com",
		"dacounter.com",
		"d.adroll.com",
		"daehaegroup.com",
		"daguogroup.com",
		"daizheha.com",
		"dajiashige.com",
		"dakic-ia-300.com",
		"danban.com",
		"dancecourt.com",
		"dano.net.cn",
		"dapper.net",
		"dapxonuq.ru",
		"darkermindz.com",
		"darknesta.com",
		"dasezhan8.com",
		"dasezhanwang.com",
		"dasretokfin.com",
		"databased.com",
		"datashreddergold.com",
		"dataxu.com",
		"dawnsworld.mysticalgateway.com",
		"daxia123.cn",
		"dbbkaidian.com",
		"dbbsrv.com",
		"dcabkl.com",
		"dccallers.org",
		"dcfmmlauksthovz.com",
		"dc-storm.com",
		"dcxbmm.com",
		"ddkoo.com",
		"ddlczn.com",
		"ddos.93se.com",
		"dd-seo.cn",
		"de007.net",
		"de17a.com",
		"dealdotcom.com",
		"deanmediagroup.com",
		"debtbusterloans.com",
		"decknetwork.net",
		"dedahuagong.com",
		"dedicatedmedia.com",
		"defygravity.com",
		"deguta.beidahuangheifeng.com",
		"deliciousdiet.ru",
		"deloo.de",
		"deltagroup.kz",
		"demandbase.com",
		"demodomain.cz",
		"depilflash.tv",
		"deposito.traffic-advance.net",
		"derekthedp.com",
		"deunce68rtaint.rr.nu",
		"devman.org",
		"dev.no8.cc",
		"dfclamp.com",
		"dfdsfadfsd.com",
		"dfdsfsdfasdf.com",
		"dfg.boutiquedepro.net",
		"dfml2.com",
		"dfzf.net",
		"dgbangyuan.cn",
		"dgdaerxing.com",
		"dgpaotui.com",
		"dgwzzz.com",
		"dgy5158.com",
		"dharold.com",
		"di1.shopping.com",
		"diaflora.hu",
		"dialerporn.com",
		"diansp.com",
		"diboine.com",
		"didtheyreadit.com",
		"die-hauensteins.com",
		"dietsante.net",
		"dikesalerno.it",
		"din8win7.in",
		"dingew.com",
		"dinkelbrezel.de",
		"dionneg.com",
		"direcong.com",
		"directaclick.com",
		"directivepub.com",
		"directleads.com",
		"directlinkq.cn",
		"directorym.com",
		"directplugin.com",
		"directtrack.com",
		"direct-xxx-access.com",
		"disco-genie.co.uk",
		"discountclick.com",
		"displayadsmedia.com",
		"displaypagerank.com",
		"dist.belnk.com",
		"dittel.sk",
		"divecatalina.com",
		"diwangjt.com",
		"djcalvin.com",
		"dj-cruse.de",
		"djfsml.com",
		"dj-sx.com",
		"djxmmh.xinhua800.cn",
		"dl.admon.cn",
		"dl.bzgthg.com",
		"dlorganic.com",
		"dlslw.com",
		"dm599.com",
		"dmtracker.com",
		"dmtracking2.alibaba.com",
		"dmtracking.alibaba.com",
		"dmwq.com",
		"dnads.directnic.com",
		"dn-agrar.nl",
		"dnaofsuccess.net",
		"dnliren.com",
		"dns-vip.net",
		"doctorsdirectory.net",
		"doctorvj.com",
		"dog.halfbirthdayproducts.com",
		"dok.do",
		"domaining.in",
		"domainsponsor.com",
		"domainsteam.de",
		"domdex.com",
		"dom-marzen.eu",
		"dongsungmold.com",
		"do-not-tracker.org",
		"dookioo.com",
		"dortxn.com",
		"do.sdu68.com",
		"dotomi.com",
		"douate.com",
		"doubleclick.com",
		"doubleclick.de",
		"doubleclick.net",
		"doublepimp.com",
		"doudouguo.com",
		"down.0551fs.com",
		"downcdn.in",
		"down.cdnxiazai.pw",
		"down.cdnxiazai.ren",
		"down.cdyb.net",
		"down.downcdn.me",
		"downflvplayer.com",
		"downlaod1.vstart.net",
		"downlaodvideo.net",
		"downlaod.vstart.net",
		"downlaod.xiaocen.com",
		"download.58611.net",
		"downloadadvisory.com",
		"downloadally.com",
		"download.cdn.0023.78302.com",
		"downloadcypher.com",
		"downloaddash.com",
		"download.dns-vip.net",
		"downloadedsoftware.com",
		"downloadespe.com",
		"downloadfused.com",
		"downloadlo.com",
		"downloadoc.com",
		"downloadold.xiaocen.com",
		"downloadprivate.com",
		"downloadri.com",
		"downloadscanning.com",
		"download.suxiazai.com",
		"downloadthesefile.com",
		"downloadthesefiles.org",
		"downloadvendors.com",
		"download.yuyu.com",
		"down.meituview.com",
		"downtownturkeytravel.com",
		"down.tututool.com",
		"down.xiazai2.net",
		"dpgjjs.com",
		"dqfix.org",
		"drawbrid.ge",
		"drc-egypt.org",
		"dreamdrama.tv",
		"drewex.slask.pl",
		"drivewaycleaninghatfield.co.uk",
		"drm.licenseacquisition.org",
		"drteachme.com",
		"drumcash.com",
		"dsds-art.com",
		"dsf.10eurosbonheur.org",
		"dsf.academiebooks.org",
		"dsg.affaireenligne.org",
		"d.srui.cn",
		"dssct.net",
		"dsyxzl.com",
		"dtdn.cn",
		"dtsrd.gov.cn",
		"dtstesting.com",
		"duchieu.de",
		"dugoutreport.com",
		"dusmin.com",
		"dvmyanmar.com",
		"dvyiub.com",
		"dwcentre.nl",
		"dwcreations.net",
		"dwdpi.co.kr",
		"dwnloader.com",
		"dwttmm.com",
		"dxcrystal.com",
		"dxinxn.com",
		"dxipo.com",
		"dygc.com",
		"dyhtez.com",
		"dynamic.fmpub.net",
		"dytt8.org",
		"dzbk.dhxctzx.com",
		"dzynestudio.neglite.com",
		"e2bworld.com",
		"eadexchange.com",
		"e-adimages.scrippsnetworks.com",
		"earnify.com",
		"eas.almamedia.fi",
		"eastmountinc.com",
		"easyhits4u.com",
		"e-bannerx.com",
		"ebara.cc",
		"ebayadvertising.com",
		"ebocornac.com",
		"ebuzzing.com",
		"ecdlszczecin.eu",
		"ecdrums.com",
		"ecircle-ag.com",
		"eclick.vn",
		"eclickz.com",
		"ecoupons.com",
		"e-cte.cn",
		"edchiu.com",
		"e-debtconsolidation.com",
		"edge.bayanazdirandamla.com",
		"edgeio.com",
		"edsse.com",
		"eduardohaiek.com",
		"education1.free.fr",
		"effectivemeasure.com",
		"effectivemeasure.net",
		"egg.formationpros.net",
		"eggfred.com",
		"ehealthcaresolutions.com",
		"eiqikan.com",
		"eiv.baidu.com",
		"e.kde.cz",
		"electrest.net",
		"electromorfosis.com",
		"e-lena.de",
		"eliav.cz",
		"elite-bijou.com.ua",
		"elitedollars.com",
		"elitesecuritypro.com",
		"elitetoplist.com",
		"eloyed.com",
		"elpatodematapalo.com",
		"el-puebloquetantodi.com.ve",
		"emarketer.com",
		"embedor.com",
		"embrari-1.cn",
		"emdadrccar.com",
		"emediate.dk",
		"emediate.eu",
		"e-m.fr",
		"emonitor.takeit.cz",
		"empe3net7.neostrada.pl",
		"empoweringinternationalministries.org",
		"end70.com",
		"engagebdr.com",
		"engine.awaps.net",
		"engine.espace.netavenir.com",
		"enginenetwork.com",
		"english.ahzh-pv.com",
		"en.hd8888.com",
		"en.minormetal.cn",
		"en.ntdzkj.com",
		"enoratraffic.com",
		"enquisite.com",
		"ensenadasportfishing.com",
		"entercasino.com",
		"e-n-t-e-r-n-e-x.com",
		"enticemetwo.yzwebsite.com",
		"entrecard.s3.amazonaws.com",
		"eoxzjk.com",
		"epiccash.com",
		"epi-spa.com",
		"e-planning.net",
		"eplarine.com",
		"eqads.com",
		"equip.yaroslavl.ru",
		"eqworks.com",
		"erg.boutiquedepro.net",
		"erg.cyberebook.info",
		"ericzworkz.free.fr",
		"ero-advertising.com",
		"errordoctor.com",
		"ertyu.com",
		"esassociacao.org",
		"esat.com.tr",
		"esellerate.net",
		"estat.com",
		"estudiobarco.com.ar",
		"esuks.com",
		"esvkxnpzlwth5f.com",
		"e-taekwang.com",
		"etahub.com",
		"etargetnet.com",
		"etbld.com",
		"ethicalads.net",
		"etnkorea.com",
		"etracker.de",
		"ets-grup.com",
		"etstemizlik.com",
		"ett.swpu.edu.cn",
		"etxlzx.net",
		"eu1.madsone.com",
		"eu-adcenter.net",
		"eubuild.com",
		"eur.a1.yimg.com",
		"eurekster.com",
		"euro3d.eu",
		"euroasia-p.com",
		"euroclick.com",
		"eurocompkft.hu",
		"eurolatexthai.com",
		"euro-linkindex.de",
		"euromerltd.com",
		"european-toplist.de",
		"euroranking.de",
		"euros4click.de",
		"eusta.de",
		"evasive.expertwitnessautomaticdoor.net",
		"everesttech.net",
		"evergage.com",
		"everton.com",
		"evidencecleanergold.com",
		"evilstalin.https443.net",
		"eviltracker.net",
		"evlilikfoto.com",
		"evodownload.com",
		"ewbio.cn",
		"ewebcounter.com",
		"ewubo.net",
		"exbaiduer.com",
		"excelwebs.net",
		"exchangead.com",
		"exchange.bg",
		"exchangeclicksonline.com",
		"exchange-it.com",
		"exit76.com",
		"exitexchange.com",
		"exitfuel.com",
		"exoclick.com",
		"exogripper.com",
		"experteerads.com",
		"exponential.com",
		"express-submit.de",
		"extractorandburner.com",
		"extreme-dm.com",
		"extremetracking.com",
		"eyeblaster.com",
		"eyereturn.com",
		"eyesondesign.net",
		"eyeviewads.com",
		"eyewonder.com",
		"ezhune.com",
		"eztexting.com",
		"ezula.com",
		"f5biz.com",
		"fabiocaminero.com",
		"fairfu.com",
		"faithbibleweb.org",
		"falconexport.com",
		"falconsafari.com",
		"faloge.com",
		"falsewi.com",
		"fancycake.net",
		"fangqianghuaye.com",
		"fantasycomments.org",
		"fap2babes.com",
		"fashion-ol.com.pl",
		"fas.nirmala.life",
		"fast-adv.it",
		"fastclick.com",
		"fastclick.com.edgesuite.net",
		"fastclick.net",
		"fasthealthycare.com",
		"favourlinks.com",
		"fb-promotions.com",
		"fbuf.cn",
		"fchabkirchen-frauenberg.de",
		"fclyon.basket.free.fr",
		"fcssqw.com",
		"fc.webmasterpro.de",
		"fdblgzwoaxpzlqus9i.com",
		"fdg.10eurosbonheur.net",
		"fdkcwl.com",
		"fdp-stjohann-ost.de",
		"fdsvmfkldv.com",
		"fecasing.com",
		"federaciondepastores.com",
		"feedbackresearch.com",
		"feedjit.com",
		"feenode.net",
		"feieo.com",
		"feilongjiasi.com",
		"feixiangpw.com",
		"fejsbuk.com.ba",
		"fengshangtp.net",
		"fengshuijia.com.cn",
		"fenshaolu.com.cn",
		"fentiaoji.cn",
		"festival.cocobau.com",
		"fetish-art.net",
		"ffeifh.com",
		"fffddd11.cn",
		"ffsi.info",
		"ffxcam.fairfax.com.au",
		"fg.bibleandbullets.com",
		"fhlyou.net",
		"fiberastat.com",
		"fideln.com",
		"fightagent.ru",
		"fiksu.com",
		"file.mm.co.kr",
		"fileserver.co.kr",
		"filesfordownloadfaster.com",
		"filmingphoto.com",
		"filmschoolsforum.com",
		"fimc.net",
		"fimserve.com",
		"finance.b3p.cn",
		"findapple.ru",
		"findbestvideo.com",
		"findcommerce.com",
		"findyourcasino.com",
		"fineclicks.com",
		"fircecymbal.com",
		"fireflypeople.ru",
		"firehorny.com",
		"firoznadiadwala.com",
		"firstbaptisthuntington.org",
		"firstlightera.com",
		"first.nova.cz",
		"first-ware.com",
		"fishum.com",
		"fjlhh.com",
		"fjronmao.com",
		"fkct.com",
		"fkdpzz.com",
		"fkj8.com",
		"fkjxzzc.com",
		"flamingowrestling4.com",
		"flashtalking.com",
		"fleshlightcash.com",
		"flexbanner.com",
		"flipsphere.ru",
		"flipvine.com",
		"floridayachtpartners.com",
		"flowgo.com",
		"floworldonline.com",
		"fl.paddletheplanet.com",
		"flurry.com",
		"fm120.com",
		"fm588.com",
		"fnyoga.biz",
		"folkspants.com",
		"fonecta.leiki.com",
		"foo.cosmocode.de",
		"foodiescooking.com",
		"foodstests.com",
		"forex-affiliate.net",
		"formationpros.net",
		"forum.d99q.cn",
		"fotxesl.com",
		"foxionserl.com",
		"fpctraffic2.com",
		"fpctraffic.com",
		"fqsjzxyey.com",
		"fragmentserv.iac-online.de",
		"frankfisherfamily.com",
		"freebanner.com",
		"free-banners.com",
		"freelogs.com",
		"freemasstraffic.com",
		"freemyapps.com",
		"freeolders.com",
		"freeonlineusers.com",
		"freepay.com",
		"freestats.com",
		"freestats.tv",
		"freewebcounter.com",
		"freewl.xinhua800.cn",
		"freightmatellc.com",
		"friendsofkannur.com",
		"frigonare.com",
		"fromform.net",
		"fromgoddesstogod.com",
		"fs-11.com",
		"fsagkp.com",
		"f-scripts.co.nr",
		"fshanyan.com",
		"fshdmc.com",
		"fshonly.com",
		"fshwb.com",
		"fsjxc.com",
		"fslhtk.com",
		"fsqiaoxin.com",
		"fsslg.com",
		"fstuoao.com",
		"f-sy.com",
		"fszls.com",
		"ftp-identification.com",
		"ftp.oldfortress.net",
		"fud.cn",
		"fuel-science-technology.com",
		"fumadosdouro.pt",
		"fungshing.com.hk",
		"funklicks.com",
		"funpageexchange.com",
		"fuqi3p.com",
		"fuqiaiai.com",
		"fusionads.net",
		"fusionquest.com",
		"fwmrm.net",
		"fxclix.com",
		"fxpcw.com",
		"fxstyle.net",
		"fybw.net.cn",
		"fyqydogivoxed.com",
		"g6tk.com",
		"gaagle.name",
		"gabriellerosephotography.com",
		"gad.dj4b9gy.top",
		"gaiaidea.com",
		"galaxien.com",
		"galleries.securesoft.info",
		"gallerycrush.com",
		"galliagroup.com",
		"game-advertising-online.com",
		"gamegoldonline.in",
		"gamehouse.com",
		"gamejil.com",
		"gamesites100.net",
		"gamesites200.com",
		"gamesitestop100.com",
		"gangda.info",
		"gao1122.com",
		"gaohaiying.com",
		"gassystem.co.kr",
		"gator.com",
		"gavih.org",
		"gayadnetwork.com",
		"gazgaped778.com",
		"gbanners.hornymatches.com",
		"gclabrelscon.net",
		"gdby.com.cn",
		"gddgjc.com",
		"gddingtian.com.cn",
		"gdeea.cc",
		"gdhrjn.com",
		"gdtrbxg.com",
		"gdzjco.com",
		"ge365.net",
		"geekograffi.com",
		"gemius.pl",
		"genconnectmentor.com",
		"gen-ever.com",
		"genih-i-nevesta.ru",
		"geobanner.adultfriendfinder.com",
		"geo.digitalpoint.com",
		"geovisite.com",
		"ger.bibliebooks.org",
		"ger.clicebooks.org",
		"gerenfa.chungcheng.net",
		"gerhard-schudok.de",
		"german-linkindex.de",
		"getclicky.com",
		"getexceptional.com",
		"ggaibb.com",
		"ggaimmm.com",
		"ggwwquzxdkaqwerob3-dd257mbsrsenuindsps.dsnxg.57670.net",
		"ghgmtcrluvghlwc91.com",
		"ghidneamt.ro",
		"ghost8.cn",
		"ghura.pl",
		"gigaia.com",
		"gijsqj.com",
		"gillingscamps.co.uk",
		"gilmoregirlspodcast.com",
		"ginot-yam.com",
		"gitinge.com",
		"gjysjl.com",
		"gkcy003.com",
		"globalismedia.com",
		"globalnursesonline.com",
		"globaltakeoff.net",
		"globaltrack.com",
		"globe7.com",
		"globus-inter.com",
		"glondis.cn",
		"glyh.net",
		"gmads.net",
		"goadservices.com",
		"go-clicks.de",
		"god123.cn",
		"gogofly.cjb.net",
		"goingplatinum.com",
		"go.jxvector.com",
		"gold-apple.net",
		"goldspotmedia.com",
		"goldstats.com",
		"gold.weborama.fr",
		"goldyoung.com",
		"golfsource.us",
		"goog1eanalitics.pw",
		"googlanalytics.ws",
		"google20.net",
		"googleadservices.com",
		"google-anallytics.com",
		"google--analytics.com",
		"google-analytics.com",
		"googleleadservices.cn",
		"google.maniyakat.cn",
		"googlesyndication.com",
		"googlle.in",
		"gool.frieghtiger.com",
		"goooogleadsence.biz",
		"go-rank.de",
		"goroomie.com",
		"gostats.com",
		"gouddc.com",
		"goyalgroupindia.com",
		"goztepe-cilingir.com",
		"gp.dejanews.com",
		"gpr.hu",
		"gpstctx.com",
		"gqwhyjh.com",
		"graficasseryal.com",
		"grafstat.ro",
		"granmaguey.com",
		"grapeshot.co.uk",
		"greatbookswap.net",
		"greenculturefoundation.org",
		"greystripe.com",
		"grk6mgehel1hfehn.ru",
		"growyourlikes.org",
		"gsimon.edu.free.fr",
		"gsiworld.neostrada.pl",
		"gstats.cn",
		"gt-office.com",
		"gtop100.com",
		"g.topguang.com",
		"gtop.ro",
		"gtp20.com",
		"gtsads.com",
		"gtsmobi.com",
		"guajfskajiw.43242.com",
		"guangdelvyou.com",
		"guerar6.org",
		"guidelineservices.com.qa",
		"guide-pluie.com",
		"guihua-china.com",
		"gumblar.cn",
		"gunibox.com",
		"gun.vrfitnesscoach.com",
		"guppymedia.com",
		"guyjin.me",
		"guyouellette.org",
		"gxatatuning.cn",
		"gxguguo.com",
		"gxqyyq.com",
		"gxwpjc.com",
		"gxxmm.com",
		"gxxyb.net",
		"gzdywz.com",
		"gzjjtz.com",
		"gzknx.com",
		"gzlightinghotel.com",
		"gzqell.com",
		"gztianfu.net",
		"gzxxzy.com",
		"gzyuhe.com",
		"h148.cn",
		"habrion.cn",
		"haedhal.com",
		"haihuang-audio.com",
		"haitaotm.com",
		"haixingguoji.com",
		"hamloon.com",
		"hanndec.com",
		"hanyueyr.com",
		"hao1680.com",
		"hao1788.cn",
		"hao368.com",
		"haoxikeji.com",
		"haphuongfoundation.net",
		"hardpornoizle.net",
		"harrenmedia.com",
		"harrenmedianetwork.com",
		"hashmi.webdesigning.name",
		"havamedia.net",
		"hayday.topapk.mobi",
		"hb4x4.com",
		"hbcbly.com",
		"hbckissimmee.org",
		"hbweiner.org",
		"hbwxzyy.com",
		"hd8888.com",
		"hdchd.org",
		"hdhaoyunlai.com",
		"hdmtxh.com",
		"hdrart.co.uk",
		"hdrhsy.cn",
		"hdxxpp.com",
		"hdyj168.com.cn",
		"heb6.com",
		"hecs.com",
		"heias.com",
		"heicha800.com",
		"heiyingkkk.com",
		"helaw.net",
		"help1comp.ru",
		"helpformedicalbills.com",
		"helpkaden.org",
		"henanct.com",
		"hengjia8.com",
		"hengyongonline.com",
		"hentaicounter.com",
		"hentainotits.com",
		"hentelpower.com",
		"heoeee.com",
		"herbalaffiliateprogram.com",
		"herbaveda.ru",
		"here.com",
		"het-havenhuis.nl",
		"hewitwolensky.com",
		"hexi100.com",
		"hexusads.fluent.ltd.uk",
		"heyos.com",
		"heywire.com",
		"hfjianghe.com",
		"hfxianghai.com",
		"hgads.com",
		"hgbyju.com",
		"hgqzs.com",
		"hhazyy.com",
		"hhetqpirahub4.com",
		"hhgk120.net",
		"hhj3.cn",
		"hi7800.com",
		"hi8.ss.la",
		"hidden.gogoceleb.com",
		"highstreeters.com",
		"hightrafficads.com",
		"hihimn.com",
		"hillcrestmemorialpark.org",
		"histats.com",
		"hit.bg",
		"hitbox.com",
		"hitcents.com",
		"hitexchange.net",
		"hitfarm.com",
		"hitiz.com",
		"hitlist.ru",
		"hitlounge.com",
		"hitometer.com",
		"hit-parade.com",
		"hit-ranking.de",
		"hits4me.com",
		"hits4pay.com",
		"hit-senders.cn",
		"hits.europuls.eu",
		"hits.informer.com",
		"hitslink.com",
		"hits.puls.lv",
		"hits.theguardian.com",
		"hittail.com",
		"hit.ua",
		"hit.webcentre.lycos.co.uk",
		"hjgk.net",
		"hjnvren.com",
		"hkfg.net",
		"hlf007.com",
		"hlzx8.com",
		"hncopd.com",
		"hnditu.com",
		"hnitat.com.cn",
		"hnsytgl.com",
		"hntldgk.com",
		"hnxinglu.com",
		"hnzpjx.com",
		"hnzt56.com",
		"hoaoyo.com",
		"hobbyworkshop.com",
		"hockeysubnantais.free.fr",
		"hollandbusinessadvertising.nl",
		"homecraftfurniture.com",
		"homeinteriorsbydesignllc.com",
		"home.jatxh.cn",
		"homely.gutterheaters4u.com",
		"homepageking.de",
		"homtextile.click79.com",
		"hongdengqu123.com",
		"honghuamm.com",
		"honlpvc.com",
		"hosse-neuenburg.de",
		"hostedads.realitykings.com",
		"hostiraj.info",
		"hosttrakker.info",
		"hotkeys.com",
		"hotlog.ru",
		"hotrank.com.tw",
		"hot-sextube.com",
		"hotslotpot.cn",
		"howtocash.com",
		"hp-h.us",
		"hq258.com",
		"hryspap.cn",
		"hsmsxx.com",
		"hsych.com",
		"htmlhubing.xyz",
		"htpm.com.cn",
		"httpool.com",
		"https443.net",
		"htxvcl.com",
		"htyzs.cn",
		"huagumei.com",
		"huakaile88.com",
		"huangjintawujin.cn",
		"huaqiangutv.com",
		"huaqiaomaicai.com",
		"huate.hk",
		"huatongchuye.com",
		"huaxiagongzhu.com",
		"huaxingee.com",
		"huayangjd.com",
		"huidakms.com.cn",
		"hujnsz.com",
		"humandemand.com",
		"humanding.com",
		"humfzz.com",
		"hunvlang.com",
		"hurricanedigitalmedia.com",
		"hvo1000.com",
		"hx018.com",
		"hx304bxg.com",
		"hxahv.com",
		"hydfood.net",
		"hydramedia.com",
		"hydrochemie.info",
		"hyjinlu.cn",
		"hyl-zh.lentor.net",
		"hyperbanner.net",
		"hypertracker.com",
		"hywczg.com",
		"hz-lf.com",
		"hzm6.com",
		"i1img.com",
		"i1media.no",
		"iad.anm.co.uk",
		"iadctest.qwapi.com",
		"iadnet.com",
		"iadsdk.apple.com",
		"ia.iinfo.cz",
		"iamartisanshop.com",
		"iasds01.com",
		"ibookschool.co.kr",
		"ibw.co.kr",
		"icailing.com",
		"icemed.net",
		"iciiran.com",
		"i-clicks.net",
		"iconadserver.com",
		"icptrack.com",
		"icqcskj.com",
		"ictcmwellness.com",
		"idcln.com",
		"idcounter.com",
		"iddiction.com",
		"identads.com",
		"idkqzshcjxr.com",
		"idot.cz",
		"idregie.com",
		"idtargeting.com",
		"iebar.t2t2.com",
		"ientrymail.com",
		"iesnare.com",
		"ifa.tube8live.com",
		"ifighi.net",
		"ifindwholesale.com",
		"ifix8.com",
		"ifrek.com",
		"igmarealty.ru",
		"ihoosq.com",
		"iiidown.com",
		"ilbanner.com",
		"ilead.itrack.it",
		"iliillliO00OO0.321.cn",
		"illaboratoriosrl.it",
		"i-lookup.com",
		"iloopmobile.com",
		"ilovecheating.com",
		"ilovespeedbumps.com",
		"im900.com",
		"imageads.canoe.ca",
		"imagecash.net",
		"images-pw.secureserver.net",
		"images.v3.com",
		"imarketservices.com",
		"imatmobile.com",
		"imax3d.info",
		"img.prohardver.hu",
		"imgpromo.easyrencontre.com",
		"img.securesoft.info",
		"imimobile.com",
		"imitrk.com",
		"imonitor.nethost.cz",
		"impactmobile.com",
		"impliedscripting.com",
		"import188.com",
		"imprese.cz",
		"impressionmedia.cz",
		"impressionz.co.uk",
		"imrworldwide.com",
		"imxpmw.com",
		"inaltravel.ru",
		"inboxdollars.com",
		"incentaclick.com",
		"indexjs.ru",
		"indexstats.com",
		"indianmediagroup.com",
		"indiatouragency.com",
		"indieclick.com",
		"indochinanetwork.com",
		"indogator.com",
		"industrialtrainingzirakpur.com",
		"industrybrains.com",
		"ineihan.cc",
		"inent17alexe.rr.nu",
		"inetlog.ru",
		"inet-poisk.ru",
		"infinite-ads.com",
		"infinityads.com",
		"infolinks.com",
		"information.com",
		"ink.churchofthefreespirit.com",
		"inmobi.com",
		"innatek.com",
		"inner-active.com",
		"inner-active.mobi",
		"inringtone.com",
		"insightexpressai.com",
		"insightexpress.com",
		"inspectorclick.com",
		"inspirenetworks.in",
		"installationsafe.net",
		"install.multinstaller.com",
		"install.securesoft.info",
		"instantmadness.com",
		"intelliads.com",
		"intellitxt.com",
		"interactive-assets.s3.amazonaws.com",
		"interactive.forthnet.gr",
		"interfere.marionunezcampusano.com",
		"intergi.com",
		"interior-examples.ru",
		"internationalclubperu.com",
		"internetfuel.com",
		"interreklame.de",
		"interstat.hu",
		"interstitial.powered-by.securesoft.info",
		"inuvi.com",
		"investice-do-nemovitosti.eu",
		"io21.ru",
		"ip193.cn",
		"iperceptions.com",
		"iphonehackgames.com",
		"ipintu.com.cn",
		"ip.ro",
		"ipro.com",
		"ipwhrtmla.epac.to",
		"iqvvsi.com",
		"iracingicoaching.com",
		"iranbar.org",
		"ireklama.cz",
		"iris2009.co.kr",
		"isaac-mafi.persiangig.com",
		"italia-rsi.org",
		"itfarm.com",
		"itoito.ru",
		"itop.cz",
		"its53new.rr.nu",
		"itspecialist.ro",
		"itsptp.com",
		"its-that-easy.com",
		"ivavitavoratavit.com",
		"ivy.it",
		"ivypixel.com",
		"ivysolutions.it",
		"iwb.com.cn",
		"i.xx.openx.com",
		"izlinix.com",
		"izlinix.net",
		"j0008.com",
		"j-5.info",
		"jah.skateparkvr.com",
		"jameser.com",
		"jaminfinity.tk",
		"januaryblessed.com",
		"jatukarm-30.com",
		"jatxt.com",
		"jbeet.cjt1.net",
		"jc-c.com",
		"jcount.com",
		"jdcartoon.com",
		"jdhuaxia.com",
		"jdsemnan.ac.ir",
		"jedonkey.cjt1.net",
		"jeikungjapani.com",
		"jerkstore.dk",
		"jewoosystem.co.kr",
		"jfdyw.com",
		"jgelevator.com",
		"jiajimx.com",
		"jianxiadianshiju.cn",
		"jianyundc.com",
		"jidekanwang.com",
		"jiek04.com",
		"jielimag.com",
		"jienoo.com",
		"jieyess.com",
		"jijimn.com",
		"jijiwang123.com",
		"jiliangxing.com",
		"jilinxsw.com",
		"jinchenglamps.com",
		"jindier.com",
		"jinkads.de",
		"jipin180.com",
		"jishuitong.com",
		"jitaiqd.com",
		"jiwire.com",
		"jixnbl.com",
		"jja00.com",
		"jja11.com",
		"jja22.com",
		"jja33.com",
		"jja44.com",
		"jja66.com",
		"jja77.com",
		"jjb00.com",
		"jjb33.com",
		"jjb44.com",
		"jjb66.com",
		"jjb77.com",
		"jjb88.com",
		"jjc00.com",
		"jjc11.com",
		"jjc22.com",
		"jjc33.com",
		"jjc55.com",
		"jjc66.com",
		"jjc77.com",
		"jjd22.com",
		"jjd55.com",
		"jjdslr.com",
		"jkazaa.cjt1.net",
		"jl.chura.pl",
		"jljpbs.com",
		"jmgyhz.com",
		"jmjcdg.com",
		"jms122.cn",
		"jmstemcell.com",
		"jnhwjyw.com",
		"jnova.cjt1.net",
		"jnvzpp.sellclassics.com",
		"jnxg.net",
		"joetec.net",
		"johnfoxphotography.com",
		"joinrockmusic.com",
		"jokedollars.com",
		"jomlajavascript.ru",
		"joojin.com",
		"jornalistasdeangola.com",
		"jorpe.co.za",
		"joshi.org",
		"jq9998.com",
		"jquery-framework.com",
		"jqueryjsscript.ru",
		"js.5689.nl",
		"jsbwpg.com",
		"jscxkj.net",
		"jsep.net",
		"jshpzd.com",
		"jsngupdwxeoa.uglyas.com",
		"jspkgj.com",
		"js.securesoft.info",
		"js.union.doudouguo.com",
		"js.union.doudouguo.net",
		"js.users.51.la",
		"jsxqhr.com",
		"jsyhxx.com",
		"jszshb.com",
		"jtpk8.com",
		"jtti.net",
		"juicyads.com",
		"julylover.com",
		"julysystems.com",
		"jumptap.com",
		"junge.wang",
		"junggomania.nefficient.co.kr",
		"junjiezyc.com",
		"junshi366.com",
		"jupcmo.com",
		"justrelevant.com",
		"justwebads.com",
		"jutuanmei.com",
		"jwsc.cn",
		"jxcsteel.com",
		"jxmjyl.com",
		"jxy88.com",
		"jyhaijiao.com",
		"kafebuhara.ru",
		"kakvsegda.com",
		"kalibrium.ru",
		"kalinston.com",
		"kanika.ru",
		"kannilulu.com",
		"kanoodle.com",
		"karaszkiewicz.neostrada.pl",
		"karbonat-tlt.ru",
		"kargo.com",
		"karlast.com",
		"karumavere.com",
		"kashun.hk.cn",
		"kasyapiserve.com",
		"kat-gifts.com",
		"kekhk.com",
		"kekle58.com",
		"kendingyou.com",
		"keruicranes.com",
		"ketaohua.com",
		"ketoanhaiphong.vn",
		"ketoanthuchanh.org",
		"keymedia.hu",
		"keynotedeviceanywhere.com",
		"kfcf.co.kr",
		"khamrianschool.com",
		"khanshop.com",
		"khtn.faperta.unri.ac.id",
		"kidsghibli.com",
		"kidspalaces.com",
		"k.iinfo.cz",
		"killevo.com",
		"kindads.com",
		"kingpinmetal.com",
		"kinslate.com",
		"kisker.czisza.hu",
		"kissmetrics.com",
		"kittenstork.com",
		"kittrellglass.com",
		"kkninuo.com",
		"kkokkoyaa.com",
		"kkuumn.com",
		"kkvmaj.com",
		"kliks.nl",
		"klxtj.com",
		"kmlky.com",
		"kogirlsnotcryz.ru",
		"komoona.com",
		"kompasads.com",
		"kontera.com",
		"konto1.cal24.pl",
		"koreasafety.com",
		"kouitc.com",
		"kpzip.com",
		"krasota-olimpia.ru",
		"krisbel.com",
		"krrehw.com",
		"ksdiy.com",
		"ksdnewr.com",
		"ksh-m.ru",
		"ksnsse.com",
		"ksp.chel.ru",
		"k-techgroup.com",
		"kt-g.de",
		"ktoooo.com",
		"ktu.sv2.biz",
		"kuaiche.com",
		"kuaiyan.com.cn",
		"kuaiyinren.cn",
		"kuizhai.com",
		"kumykoz.com",
		"kusco.tw",
		"kzhqzx.com",
		"la21jeju.or.kr",
		"labconnectlc.com",
		"ladybug.gutterheatersus.com",
		"lady.qwertin.ru",
		"laextradeocotlan.com.mx",
		"lagerhaus-loft-toenning.de",
		"lagrotta4u.de",
		"laiqukeji.com",
		"lakequincy.com",
		"laliga-fans.ru",
		"lambandfox.co.uk",
		"lamtinchina.com",
		"langtupx.com",
		"lanmeishiye.com",
		"lanshanfood.com",
		"laos.luangprabang.free.fr",
		"lasimp04risoned.rr.nu",
		"laspfxb.com",
		"lastmeasure.zoy.org",
		"lauglyhousebuyers.com",
		"lawfirm.chungcheng.net",
		"layer-ad.de",
		"layer-ads.de",
		"lazycranch.us",
		"lbmm88.com",
		"lbn.ru",
		"lbsycw.com",
		"lct.salesforce.com",
		"le589.com",
		"leadaffiliates.com",
		"lead-analytics.nl",
		"leadboltads.net",
		"leadbolt.com",
		"leadclick.com",
		"leadingedgecash.com",
		"leadzupc.com",
		"lean.com",
		"leanoisgo.com",
		"lectscalimertdr43.land.ru",
		"leferinktractors.com",
		"legolas-media.com",
		"lejrvk.com",
		"lensstrap.com",
		"leonarderickson.chez.com",
		"leslascarsgays.fr",
		"leuco.com.cn",
		"leucosib.ru",
		"levelrate.de",
		"lewwwz.com",
		"lfcraft.com",
		"lfgkyy.com",
		"lfstmedia.com",
		"lhs-mhs.org",
		"liagand.cn",
		"lian-yis.com",
		"liarsbar.karoo.net",
		"liberated.org",
		"licenseacquisition.org",
		"lidaergroup.com",
		"lifenetusa.com",
		"lifestreetmedia.com",
		"liftdna.com",
		"ligatus.com",
		"ligatus.de",
		"lightningcast.net",
		"lightspeedcash.com",
		"lijapan.com",
		"lijit.com",
		"lilupophilupop.com",
		"limimi8.com",
		"lincos.net",
		"linfenit.com",
		"link2me.ru",
		"link4ads.com",
		"linkadd.de",
		"link-booster.de",
		"linkbuddies.com",
		"linkexchange.com",
		"linkexchange.ru",
		"linkprice.com",
		"linkrain.com",
		"linkreferral.com",
		"linkshighway.com",
		"linkshighway.net",
		"links-ranking.de",
		"linkstorms.com",
		"linkswaper.com",
		"linktarget.com",
		"lio888.com",
		"liquidacionessl.com",
		"liquidad.narrowcastmedia.com",
		"lisboadiadia.com",
		"lita-lighting.com",
		"little.forexbrokerstoday.info",
		"livefootball.ro",
		"liveintent.com",
		"livench.com",
		"liverail.com",
		"livinggood.se",
		"ljsyxx.cn",
		"lk5566.com",
		"llbb88.com",
		"llhan.com",
		"llo123.com",
		"lmsongnv.com",
		"lnhxwmhoyjxqmtgn9u.com",
		"lnqgw.com",
		"loading321.com",
		"lobocastleproductions.com",
		"localmantra.com",
		"localmediabuying.com",
		"localytics.com",
		"location.fashionises.com",
		"locationlook.ru",
		"lococcc.com",
		"log.btopenworld.com",
		"logua.com",
		"lolblog.cn",
		"londparig.ga",
		"longjiwybearing.com",
		"loopme.biz",
		"lop.com",
		"losalseehijos.es",
		"losingthisweight.com",
		"lousecn.cn",
		"love2068.cn",
		"lpcloudsvr302.com",
		"lpmxp2017.com",
		"lpmxp2018.com",
		"lpmxp2020.com",
		"lpmxp2022.com",
		"lpmxp2023.com",
		"lpmxp2024.com",
		"lpmxp2025.com",
		"lpmxp2026.com",
		"lpmxp2027.com",
		"lpwangzhan.com",
		"lsxsccc.com",
		"lt3456.com",
		"ltktourssafaris.com",
		"ltsetu.com",
		"lualuc.com",
		"lucidmedia.com",
		"luckys-fashion.com",
		"luckyson0660.com",
		"luguanmm.com",
		"luguanzhan.com",
		"lunarads.com",
		"lunaticjazz.com",
		"lupytehoq.com",
		"lushantouzi.com",
		"lwtzdec.com",
		"lwyzzx.cn",
		"lxsg.net",
		"lxwcollection.com",
		"lyqncy.com",
		"lysyp.com",
		"lyt99.com",
		"lzjl.com",
		"lztz.net",
		"lzxsw100.com",
		"m1d.ru",
		"m1.webstats4u.com",
		"m4n.nl",
		"m77s.cn",
		"macallinecn.com",
		"macerlighting.com",
		"madadsmedia.com",
		"madclient.uimserv.net",
		"madisonavenue.com",
		"mads.aol.com",
		"mads.cnet.com",
		"madserve.org",
		"madvertise.de",
		"mafund.cn",
		"magnetic.com",
		"mah0ney.com",
		"mail3x.com",
		"mainnetsoll.com",
		"mainstatserver.com",
		"maithi.info",
		"majuni.beidahuangheifeng.com",
		"malayalam-net.com",
		"malware-check.disconnect.me",
		"malware-scan.com",
		"mamakaffahshop.com",
		"mamivoi.com",
		"mamj.ru",
		"mammothcondorentalsca.com",
		"mampoks.ru",
		"man1234.com",
		"manage.com",
		"mandarin.aquamarineku.com",
		"maniyakat.cn",
		"mannesoth.com",
		"mans.cnusher.ind.in",
		"maoshanhouyi.cc",
		"maplefarmmedia.com",
		"marcasdelnorte.com.mx",
		"marchex.com",
		"marco-behrendt.de",
		"market-buster.com",
		"marketing.888.com",
		"marketing.hearstmagazines.nl",
		"marketing.nyi.net",
		"marketing.osijek031.com",
		"marketingsolutions.yahoo.com",
		"marketron.com",
		"maroonspider.com",
		"martuz.cn",
		"masjlr.com",
		"mas.sector.sk",
		"masterkeybeth.otbsolutionsgp.com",
		"mastermind.com",
		"maszcjc.com",
		"matchcraft.com",
		"mathtag.com",
		"matomy.com",
		"matrics.ro",
		"matthewsusmel.com",
		"matzines.com",
		"max.i12.de",
		"maximumcash.com",
		"mayatek.info",
		"mazda.georgewkohn.com",
		"mbcobretti.com",
		"mbn.com.ua",
		"mbs.megaroticlive.com",
		"mbuyu.nl",
		"mconnect.pl",
		"mdlcake.com",
		"mdotm.com",
		"me.3788.cn",
		"measuremap.com",
		"mebel.by.ru.fqwerz.cn",
		"mebelest.ru",
		"mecdot.com",
		"media6degrees.com",
		"media-adrunner.mycomputer.com",
		"mediaarea.eu",
		"mediaarmor.com",
		"mediabrix.com",
		"mediacharger.com",
		"mediadvertising.ro",
		"media.ftv-publicite.fr",
		"media.funpic.de",
		"mediageneral.com",
		"medialets.com",
		"medialytics.com",
		"mediamath.com",
		"mediamgr.ugo.com",
		"mediamind.com",
		"media.net",
		"mediaplazza.com",
		"mediaplex.com",
		"mediascale.de",
		"media-servers.net",
		"mediashakers.com",
		"mediast.eu",
		"mediatext.com",
		"mediax.angloinfo.com",
		"mediaz.angloinfo.com",
		"medio.com",
		"medleyads.com",
		"medyanetads.com",
		"meenou.com",
		"mefa.ws",
		"megacash.de",
		"megago.com",
		"megastats.com",
		"megawerbung.de",
		"meghalomania.com",
		"meigert.com",
		"meirmusic.com",
		"mekabinks.in",
		"meltdsp.com",
		"memeglobal.com",
		"memorix.sdv.fr",
		"messenger.zango.com",
		"metaffiliation.com",
		"metal-volga.ru",
		"metameets.eu",
		"metanetwork.com",
		"metanetwork.net",
		"metaresolver.com",
		"methodcash.com",
		"methuenedge.com",
		"metrics.windowsitpro.com",
		"metzgerconsulting.com",
		"mgcksa.com",
		"mgid.com",
		"mgscw.com",
		"mh-hundesport.de",
		"mhnrw.com",
		"miamibeachhotels.tv",
		"miarroba.com",
		"microsearchstat.com",
		"microsotf.cn",
		"microstatic.pl",
		"microticker.com",
		"midnightclicking.com",
		"millennialmedia.com",
		"mimascotafiel.com",
		"mimile8.com",
		"minager.com",
		"mindmemobile.com",
		"mintrace.com",
		"misegundocuadro.com",
		"miserji.com",
		"missionoch.org",
		"misstrends.com",
		"miva.com",
		"mixandbatch2000.co.uk",
		"mixpanel.com",
		"mixtraffic.com",
		"mizahturk.com",
		"mj-ive.com",
		"mjw.or.kr",
		"mkhafnorcu81.com",
		"mlm.de",
		"m.loldlxmy.com",
		"mm113.com",
		"mm58100.com",
		"mm6500.com",
		"mmaglobal.com",
		"mmedia.com",
		"mmexe.com",
		"mmismm.com",
		"mmnidy.com",
		"mmtro.com",
		"mnogobab.com",
		"mnshdq.com",
		"mnxgz.com",
		"moacbeniv.com",
		"moadnet.com",
		"moaramariei.ro",
		"moatads.com",
		"mobcdn.com",
		"mobclix.com",
		"mobday.com",
		"mobfox.com",
		"mobgold.com",
		"mobhero.com",
		"mobilda.com",
		"mobileactive.com",
		"mobileadvertisinghub.com",
		"mobileapptracking.com",
		"mobile-collector.newrelic.com",
		"mobilecomputingtoday.com",
		"mobile-content.info",
		"mobile-ent.biz",
		"mobilefuse.nu",
		"mobilemessenger.com",
		"mobileposse.com",
		"mobile-safety.org",
		"mobilestorm.com",
		"mobiletheory.com",
		"mobilewithsms.net",
		"mobivity.com",
		"mobixell.com",
		"moblao.com",
		"mobstac.com",
		"mobuna.com",
		"moby-aa.ru",
		"mobyt.com",
		"mocean.mobi",
		"moceanmobile.com",
		"modijie.com",
		"mogreet.com",
		"mogyang.net",
		"mojiva.com",
		"monarchexcess2.com",
		"monetizemore.com",
		"moneyexpert.com",
		"monidopo.bee.pl",
		"monsterpops.com",
		"month.nualias.com",
		"moolahmedia.com",
		"moontag.com",
		"moo.parenthoodvr.com",
		"mopub.com",
		"morenewmedia.com",
		"motionritm.ru",
		"motricity.com",
		"motrixi.com",
		"mouseflow.com",
		"movak.sk",
		"moversa.com",
		"mp3-pesni.ru",
		"mpif.eu",
		"mpstat.us",
		"mqwdaq.com",
		"mrappolt.de",
		"mr-rank.de",
		"mrskincash.com",
		"mslogs.com",
		"msw67.cafe24.com",
		"mtmoriahcogic.org",
		"mtree.com",
		"mtsx.com.cn",
		"muglaulkuocaklari.org",
		"mulbora.com",
		"musiccounter.ru",
		"mutex.ru",
		"muwmedia.com",
		"mvnvpic.com",
		"mvxiui.com",
		"m.webtrends.com",
		"mxyyth.com",
		"my5525.net",
		"myaffiliateprogram.com",
		"mybloglog.com",
		"mybuzzmonitor.com",
		"mycounter.ua",
		"mydas.mobi",
		"myeverydaylife.net",
		"myfileupload.ru",
		"mygooglemy.com",
		"myhemorrhoidtreatment.com",
		"mykhyber.org",
		"mylada.ru",
		"mylftv.com",
		"mynetav.net",
		"mypagerank.net",
		"mypagerank.ru",
		"mypowermall.com",
		"myscreen.com",
		"mysimash.info",
		"mystat-in.net",
		"mystat.pl",
		"mystictravel.org",
		"mythings.com",
		"mytop-in.net",
		"n69.com",
		"n85853.cn",
		"naiadsystems.com",
		"nainasdesigner.com",
		"naj.sk",
		"namemaster46.net",
		"namimedia.com",
		"nancunshan.com",
		"narbhaveecareers.com",
		"nastydollars.com",
		"natakocharyan.ru",
		"natebennettfleming.com",
		"nationalsecuritydirect.com",
		"navigator.io",
		"navrcholu.cz",
		"nba1001.net",
		"nbjmp.com",
		"ncenterpanel.cn",
		"ndparking.com",
		"nedstatbasic.net",
		"nedstat.com",
		"nedstat.nl",
		"nedstatpro.net",
		"neepelsty.cz.cc",
		"neglite.com",
		"negociermonhypotheque.com",
		"neilowen.org",
		"nend.net",
		"neobake.com",
		"neocounter.neoworx-blog-tools.net",
		"neoffic.com",
		"net4um.com",
		"netaffiliation.com",
		"netagent.cz",
		"netclickstats.com",
		"netcommunities.com",
		"netdirect.nl",
		"net-filter.com",
		"netflame.cc",
		"netincap.com",
		"netmng.com",
		"netpool.netbookia.net",
		"netseer.com",
		"netshelter.net",
		"network.business.com",
		"neudesicmediagroup.com",
		"newads.bangbros.com",
		"newasp.com.cn",
		"newbie.com",
		"newelavai.com",
		"newnet.qsrch.com",
		"newnudecash.com",
		"newopenx.detik.com",
		"newstudy.net",
		"newt1.adultadworld.com",
		"newt1.adultworld.com",
		"newtopsites.com",
		"nexac.com",
		"nexage.com",
		"nexprice.com",
		"nextlevellacrosse.com",
		"ng3.ads.warnerbros.com",
		"ngr61ail.rr.nu",
		"ngs.impress.co.jp",
		"nikjju.com",
		"nimp.org",
		"ninjafy.com",
		"nitroclicks.com",
		"nje1.cn",
		"nje9.cn",
		"njszny.com",
		"nminmobiliaria.com",
		"nokiastock.ru",
		"nonoknit.com",
		"nonrisem.com",
		"norton-scan-mobile.com",
		"novem.pl",
		"noviasconglamourenparla.es",
		"nro.gov.sd",
		"nt002.cn",
		"ntdfbp.com",
		"ntkrnlpa.cn",
		"nuggad.net",
		"numax.nu-1.com",
		"nuseek.com",
		"nuterr.com",
		"nuvhxc.com",
		"nvplv.cc",
		"nwhomecare.co.uk",
		"nycsoaw.org",
		"nyskiffintabout.com",
		"oa.pelagicmall.com.cn",
		"oas.benchmark.fr",
		"oascentral.businessweek.com",
		"oascentral.chicagobusiness.com",
		"oascentral.fortunecity.com",
		"oascentral.register.com",
		"oas.foxnews.com",
		"oas.repubblica.it",
		"oas.roanoke.com",
		"oas.salon.com",
		"oas.toronto.com",
		"oas.uniontrib.com",
		"oas.villagevoice.com",
		"obdeskfyou.ru",
		"ocat84einc.rr.nu",
		"oceanic.ws",
		"ocnmnu.com",
		"odmarco.com",
		"oewa.at",
		"oewabox.at",
		"offended.feenode.net",
		"offerforge.com",
		"offerfusion.com",
		"offermatica.com",
		"offline.dyd-pascal.com",
		"ohgooo.com",
		"ohhdear.org",
		"oisrup.com",
		"ojakobi.de",
		"ojaofs.com",
		"okboobs.com",
		"oko1122.com",
		"oktits.com",
		"olcme.yildiz.edu.tr",
		"oldicbrnevents.com",
		"old.yesmeskin.co.kr",
		"olivebrandresponse.com",
		"olivier.goetz.free.fr",
		"oliwei.com",
		"omgates.com",
		"omniture.com",
		"omrtw.com",
		"onclasrv.com",
		"onclickads.net",
		"oneandonlynetwork.com",
		"oneil-clan.com",
		"onenetworkdirect.com",
		"onestat.com",
		"onestatfree.com",
		"onewaylinkexchange.net",
		"onfreesoftware.com",
		"onlinecash.com",
		"onlinecashmethod.com",
		"onlinedetect.com",
		"onlinegy7uj.co.uk",
		"online-metrix.net",
		"onlinerewardcenter.com",
		"onlinetribun.com",
		"on-mobi.com",
		"onmobile.com",
		"onthenetas.com",
		"openads.friendfinder.com",
		"openads.org",
		"openad.tf1.fr",
		"openad.travelnow.com",
		"openclick.com",
		"openmarket.com",
		"openx.angelsgroup.org.uk",
		"openx.blindferret.com",
		"openx.com",
		"opienetwork.com",
		"optimost.com",
		"optmd.com",
		"oqgmav.com",
		"orange.bageriethornslet.dk",
		"orcsnx.com",
		"ordingly.com",
		"orentraff.cn",
		"origin-cached.licenseacquisition.org",
		"osteklenium.ru",
		"ota.cartrawler.com",
		"otdacham.ru",
		"otto-images.developershed.com",
		"ouroldfriends.com",
		"outbrain.com",
		"out-there-media.com",
		"overtha.com",
		"overture.com",
		"ovonnn.com",
		"owebmoney.ru",
		"oxado.com",
		"oxcash.com",
		"oxen.hillcountrytexas.com",
		"oxiouo.com",
		"oxoo678.com",
		"ozarslaninsaat.com.tr",
		"oztoojhyqknbhyn8.com",
		"paalzb.com",
		"p.adpdx.com",
		"pagead.l.google.com",
		"pagefair.com",
		"pagerank4u.eu",
		"pagerank4you.com",
		"pagerank-estate-spb.ru",
		"pagerank-ranking.com",
		"pagerank-ranking.de",
		"pagerank-server7.de",
		"pagerank-submitter.com",
		"pagerank-submitter.de",
		"pagerank-suchmaschine.de",
		"pageranktop.com",
		"pagerank-united.de",
		"pairedpixels.com",
		"panthawas.com",
		"papayamobile.com",
		"paradisulcopiilortargoviste.ro",
		"paranteztanitim.com",
		"pardonmypolish.pl",
		"partage-facile.com",
		"partnerad.l.google.com",
		"partner-ads.com",
		"partnercash.de",
		"partner.pelikan.cz",
		"partners.priceline.com",
		"partner.topcities.com",
		"parttimecollegejobs.com",
		"pasakoyekmek.com",
		"pascani.md",
		"passion-4.net",
		"passportblues.ru",
		"passports.ie",
		"patogh-persian.persiangig.com",
		"pattayabazaar.com",
		"paul.cescon.ca",
		"paulsdrivethru.net",
		"pay-ads.com",
		"paycounter.com",
		"paypal.com.0.sessionid363636.sahaajans.com",
		"paypal.com.0.sessionid756756756.sahaajans.com",
		"paypal.com.0.sessionid795795795.sahaajans.com",
		"paypal.com.0.sessionid953953953.sahaajans.com",
		"paypopup.com",
		"paysafecard.name",
		"payserve.com",
		"pazarlamacadisi.com",
		"pb7.us",
		"pbnet.ru",
		"pcash.imlive.com",
		"pcbangv.com",
		"pcmaxsoftware.com",
		"pc-pointers.com",
		"pdk.lcn.cc",
		"pear.dementiaadvocacy.com",
		"peep-auktion.de",
		"peer39.com",
		"peguards.cc",
		"pempoo.com",
		"pennystock-picks.info",
		"pennyweb.com",
		"peoria33884.cz.cc",
		"pepperjamnetwork.com",
		"percentmobile.com",
		"perfectaudience.com",
		"perfiliate.com",
		"performancerevenue.com",
		"performancerevenues.com",
		"performancing.com",
		"perf.weborama.fr",
		"personalkapital.com",
		"perugemstones.com",
		"petpalacedeluxe.com.br",
		"pgmediaserve.com",
		"pgpartner.com",
		"pham.duchieu.de",
		"pheedo.com",
		"phizzle.com",
		"phluant.com",
		"phoenix-adrunner.mycomputer.com",
		"phonearena.com",
		"photomoa.co.kr",
		"photo.video.gay.free.fr",
		"phpadsnew.new.natuurpark.nl",
		"phpctuqz.assexyas.com",
		"phpmyvisites.net",
		"phpoutsourcingindia.com",
		"phunware.com",
		"picadmedia.com",
		"pickfonts.com",
		"picshic.com",
		"pillscash.com",
		"pills.ind.in",
		"pimproll.com",
		"pimpwebpage.com",
		"pinkpillar.ru",
		"pixel.adsafeprotected.com",
		"pixel.jumptap.com",
		"pizzadaily.org",
		"pizzotti.net",
		"pjhku.com",
		"placeplay.com",
		"plaidpainting.com",
		"planetactive.com",
		"planetapokera.ru",
		"platamones.nl",
		"play4traffic.com",
		"playerflv.com",
		"playhaven.com",
		"playtomic.com",
		"plethoramobile.com",
		"plista.com",
		"plmatrix.com",
		"plolgki.com.cn",
		"plugrush.com",
		"pointroll.com",
		"pokerlivestar.de",
		"pokerlounge-langenfeld.de",
		"politads.com",
		"polska.travel.pl",
		"polycliniqueroseraie.com",
		"pomosh-stydenty.ru",
		"pontiflex.com",
		"popads.net",
		"popub.com",
		"pop-under.ru",
		"popunder.ru",
		"popupmoney.com",
		"popup.msn.com",
		"popupnation.com",
		"popups.infostart.com",
		"popuptraffic.com",
		"porn-girls-nude-and-horny.com",
		"porngraph.com",
		"pornstar-candysue.de",
		"porntrack.com",
		"postrelease.com",
		"potenza.cz",
		"power.bestconstructionexpertwitness.com",
		"powerplanting.com",
		"powershopnet.net",
		"pozdrav-im.ru",
		"pqwaker.altervista.org",
		"pr5dir.com",
		"praddpro.de",
		"prchecker.info",
		"precisioncounter.com",
		"predictad.com",
		"prefer.gutterhelment.com",
		"premier-one.net",
		"premium-offers.com",
		"preview.licenseacquisition.org",
		"primaryads.com",
		"primetime.net",
		"pringlepowwow.com",
		"printronix.net.cn",
		"privatcamvideo.de",
		"privatecash.com",
		"pro-advertising.com",
		"proanalytics.cn",
		"procholuao.com",
		"prod-abc.ro",
		"proext.com",
		"profero.com",
		"profileawareness.com",
		"pro.i-doctor.co.kr",
		"projector-rental.iffphilippines.com",
		"projectwonderful.com",
		"promo1.webcams.nl",
		"promo.badoink.com",
		"promobenef.com",
		"promos.fling.com",
		"promote.pair.com",
		"promotion-campaigns.com",
		"promo.ulust.com",
		"pronetadvertising.com",
		"propellerads.com",
		"proranktracker.com",
		"prosperity.charifree.org",
		"protexting.com",
		"proton-tm.com",
		"protraffic.com",
		"provexia.com",
		"proxysite.org",
		"prsitecheck.com",
		"pr-star.de",
		"pr-ten.de",
		"psstt.com",
		"psy-ufa.ru",
		"p.toourbb.com",
		"ptpgold.info",
		"pub.chez.com",
		"pub.club-internet.fr",
		"pubdirecte.com",
		"pub.hardware.fr",
		"publicandolo.com",
		"publicidad.elmundo.es",
		"pubmatic.com",
		"pub.realmedia.fr",
		"pubs.lemonde.fr",
		"pulse360.com",
		"q1k.ru",
		"q2thainyc.com",
		"qabbanihost.com",
		"q.azcentral.com",
		"qctop.com",
		"qgmmrvbqwlouglqggi.com",
		"qgsruo.com",
		"qgtjhw.com",
		"qhhxzny.gov.cn",
		"qihv.net",
		"qii678.com",
		"qmvzlx.com",
		"qnsr.com",
		"qpxepj.com",
		"qq6500.com",
		"qqjay2.cn",
		"qqmeise.com",
		"qqxxdy.com",
		"qqzhanz.com",
		"qshfwj.com",
		"quakemarketing.com",
		"quantcast.com",
		"quantserve.com",
		"quarterserver.de",
		"questaffiliates.net",
		"quigo.com",
		"quinst.com",
		"quisma.com",
		"qwapi.apple.com",
		"qwepa.com",
		"qxkkey.com",
		"r0218.rsstatic.ru",
		"radar.cedexis.com",
		"radarurl.com",
		"radiate.com",
		"radiosouf.free.fr",
		"radiumone.com",
		"rad.msn.com",
		"rafastudio.nl",
		"rajasthantourismbureau.com",
		"rampidads.com",
		"rankchamp.de",
		"rankingchart.de",
		"ranking-charts.de",
		"ranking-hits.de",
		"ranking-id.de",
		"ranking-links.de",
		"ranking-liste.de",
		"rankingscout.com",
		"ranking-street.de",
		"rank-master.com",
		"rank-master.de",
		"rankyou.com",
		"ransun.net",
		"rapidcounter.com",
		"rate.ru",
		"ratings.lycos.com",
		"ravelotti.cn",
		"rb0577.com",
		"rb1.design.ru",
		"rbcholdings.com",
		"rcturbo.com",
		"rd.jiguangie.com",
		"reachjunction.com",
		"reactx.com",
		"readserver.net",
		"realcastmedia.com",
		"realclix.com",
		"realgrown.co",
		"realmedia-a800.d4p.net",
		"realtechnetwork.com",
		"realteencash.com",
		"realtracker.com",
		"rebisihut.com",
		"rebotstat.com",
		"recette.confiture.free.fr",
		"recruitingpartners.com",
		"redcada.com",
		"reddii.org",
		"redhotdirectory.com",
		"re-directme.com",
		"redlinecompany.ravelotti.cn",
		"redmas.com",
		"redoperabwo.ru",
		"reduxmedia.com",
		"reduxmediagroup.com",
		"reedbusiness.com",
		"reefaquarium.biz",
		"referralware.com",
		"reflexe.locationvoiture-guadeloupe.net",
		"reflexonature.free.fr",
		"regis.foultier.free.fr",
		"registry-fix-softwares.com",
		"reglasti.com",
		"regnow.com",
		"reinvigorate.net",
		"reklama.mironet.cz",
		"reklama.reflektor.cz",
		"reklamcsere.hu",
		"reklamer.com.ua",
		"reklame.unwired-i.net",
		"reklam.rfsl.se",
		"relaax.co.cc",
		"relevanz10.de",
		"relimar.com",
		"relish.com.cn",
		"relmaxtop.com",
		"reltime2012.ru",
		"reltime-2014.ru",
		"remission.tv.gg",
		"remorcicomerciale.ro",
		"remotead.cnet.com",
		"rentimeinvz.com",
		"rentminsk.net",
		"republika.onet.pl",
		"requiemfishing.com",
		"retargeter.com",
		"rev2pub.com",
		"revcontent.com",
		"revenuedirect.com",
		"revenue.net",
		"revenueonthego.com",
		"revmob.com",
		"revsci.net",
		"revstats.com",
		"reycross.cn",
		"rhythmnewmedia.com",
		"richmails.com",
		"richmedia.yimg.com",
		"richwebmaster.com",
		"rickecurepair.com",
		"rick.nirmallife.co.in",
		"rightmedia.com",
		"rightstats.com",
		"rimakaram.net",
		"ri-materials.com",
		"riotassistance.ru",
		"ristoncharge.in",
		"riwxluhtwysvnk.com",
		"rkkdlaw.com",
		"rlcdn.com",
		"rle.ru",
		"rlxl.com",
		"rmads.msn.com",
		"rmedia.boston.com",
		"rnhbhnlmpvvdt.com",
		"roar.com",
		"robert-millan.de",
		"robotreplay.com",
		"rochesterdata.com",
		"rocketfuel.com",
		"rockleadesign.com",
		"rodtheking.com",
		"roia.biz",
		"rok.com.com",
		"rokobon.com",
		"rolyjyl.ru",
		"rompaservices.com",
		"ronasiter.com",
		"roscoesrestaurant.com",
		"rose.ixbt.com",
		"rotabanner.com",
		"roxr.net",
		"royalair.koom.ma",
		"rq82.com",
		"rqdsj.com",
		"rt7890.com",
		"rtbidder.net",
		"rtbpop.com",
		"rtbpopd.com",
		"rtkgvp.com",
		"rtysus.com",
		"rtyszz.com",
		"ru4.com",
		"rubiconproject.com",
		"rurik.at.ua",
		"ru-traffic.com",
		"rvkeda.com",
		"rvwsculpture.com",
		"rythmxchange.com",
		"s2d6.com",
		"s8s8s8.com",
		"saawa.com",
		"sadkajt357.com",
		"s.adroll.com",
		"sageanalyst.net",
		"sahaajans.com",
		"sahafci.com",
		"sam-sdelai.blogspot.com",
		"samwooind.co.kr",
		"santhirasekarapillaiyar.com",
		"sarahcraig.org",
		"saraprichen.altervista.org",
		"sarepta.com.ua",
		"saunaundbad.de",
		"savingnegociacoes.com.br",
		"sbx.pagesjaunes.fr",
		"scambiobanner.aruba.it",
		"scanscout.com",
		"school-bgd.ru",
		"scientiamobile.com",
		"scoeyc.com",
		"scopelight.com",
		"scorecardresearch.com",
		"scratch2cash.com",
		"scripte-monster.de",
		"scuolaartedanza.net",
		"sc.urban1communities.com",
		"sddaiu.com",
		"sdnxmy.com",
		"sdoovo.com",
		"sdu68.com",
		"search-box.in",
		"searchfeast.com",
		"searchmarketing.com",
		"searchramp.com",
		"secitasr.holdonhosting.net",
		"secourisme-objectif-formation.fr",
		"securesoft.info",
		"secure-softwaremanager.com",
		"secure.webconnect.net",
		"sedewww.com",
		"sedoparking.com",
		"sedotracker.com",
		"seeq.com.invalid",
		"sefror.com",
		"segege.com",
		"se-group.de",
		"selak.info",
		"self-defining.com",
		"semeimeie.com",
		"senddroid.com",
		"senrima.ru",
		"sensenetworks.com",
		"sensismediasmart.com.au",
		"sentimentindia.com",
		"seo4india.com",
		"seojee.com",
		"seopoint.com",
		"seouldae.gosiwonnet.com",
		"sepung.co.kr",
		"seqsixxx.com",
		"seres.https443.net",
		"serv0.com",
		"servedbyadbutler.com",
		"servedby-buysellads.com",
		"servedbyopenx.com",
		"servethis.com",
		"service1.adten.de",
		"services.hearstmags.com",
		"serving-sys.com",
		"sessionm.com",
		"setjetters.com",
		"sexaddpro.de",
		"sexadvertentiesite.nl",
		"sexcounter.com",
		"sexfromindia.com",
		"sexinyourcity.com",
		"sexlist.com",
		"sextracker.com",
		"sexueyun.com",
		"sexyfemalewrestlingmovies-b.com",
		"sexyfemalewrestlingmovies.com",
		"sexystat.com",
		"sezwho.com",
		"shai880.com",
		"shareadspace.com",
		"shareasale.com",
		"sharepointads.com",
		"sharfiles.com",
		"shar-m.com",
		"shcpa2011.com",
		"shecanseeyou.info",
		"shema.firstcom.co.kr",
		"shenke.com.cn",
		"sher.index.hu",
		"shibanikashyap.asia",
		"shinystat.com",
		"shinystat.it",
		"shmjikrhddazenp75.com",
		"shoppingads.com",
		"sh-sunq.com",
		"shtpk.com",
		"shuangfeidyw.com",
		"shuangyanpijiage.com",
		"shuangying163.com",
		"siccash.com",
		"sicken.cede.cl",
		"sidebar.angelfire.com",
		"sightshare.com",
		"signalhq.com",
		"simplequiltmaking.com",
		"simpletexting.com",
		"simplycast.com",
		"sinoa.com",
		"sinopengelleriasma.com",
		"sisters.truyen24h.info",
		"sitebrand.geeks.com",
		"sitemerkezi.net",
		"sitemeter.com",
		"sitestat.com",
		"sixsigmatraffic.com",
		"skottles.com",
		"skovia.com",
		"skylink.vn",
		"slickaffiliate.com",
		"slicktext.com",
		"slopeaota.com",
		"smaato.com",
		"sma.punto.net",
		"smart4ads.com",
		"smartadserver.com",
		"smartbase.cdnservices.com",
		"smartdevicemedia.com",
		"smartenergymodel.com",
		"smitaasflowercatering.com",
		"smowtion.com",
		"smrrbt.com",
		"sms.otair.com",
		"snapads.com",
		"snapgiant.com",
		"snkforklift.com",
		"snoobi.com",
		"snore.sabreasiapacific.com",
		"snrp.uglyas.com",
		"socialspark.com",
		"sockslab.net",
		"softclick.com.br",
		"softh.blogsky.com",
		"soft.jbdown.net",
		"softprojects007.ru",
		"softtube.cn",
		"solo-juegos.com",
		"soluxury.co.uk",
		"songreen.com",
		"sorclan.za.pl",
		"sosplombiers-6eme.fr",
		"sosplombiers-8eme.fr",
		"sosplombiers-9eme.fr",
		"soundfyles.eloyed.com",
		"source-games.ru",
		"sowellness.be",
		"spacash.com",
		"spanishfrompauley.com",
		"sparklinktravels.net",
		"sparkstudios.com",
		"s-parta.za.pl",
		"specialistups.com",
		"specificmedia.co.uk",
		"specificpop.com",
		"spezialreporte.de",
		"spinbox.techtracker.com",
		"spinbox.versiontracker.com",
		"sponsorads.de",
		"sponsorpay.com",
		"sponsorpro.de",
		"sponsors.thoughtsmedia.com",
		"sportsbettingaustralia.com",
		"spot.fitness.com",
		"spotmarka.ap0x.com",
		"spotxchange.com",
		"sprinks-clicks.about.com",
		"spunkyvids.com",
		"spylog.com",
		"spyshredderscanner.com",
		"spywarelabs.com",
		"spywarenuker.com",
		"spywarepc.info",
		"spywareshop.info",
		"spywaresite.info",
		"spywords.com",
		"sqmeinv.com",
		"squirtvidz.com",
		"srbijacafe.org",
		"srwww1.com",
		"ssartpia.or.kr",
		"ssbo98omin.rr.nu",
		"ssl443.org",
		"sso.anbtr.com",
		"ssssd4rrr.szfuchen.com",
		"stabroom.cn",
		"stalu.sk",
		"stamfordtecnews.com",
		"star-advertising.com",
		"starffa.com",
		"startapp.com",
		"start.freeze.com",
		"stat24.com",
		"stat24.meta.ua",
		"stat.cliche.se",
		"statcounter.com",
		"stat.dealtime.com",
		"stat.dyna.ultraweb.hu",
		"stathat.com",
		"staticads.btopenworld.com",
		"static.fmpub.net",
		"static.itrack.it",
		"statistik-gallup.net",
		"statm.the-adult-company.com",
		"stat.pl",
		"stats4all.com",
		"stats.blogger.com",
		"stats.cts-bv.nl",
		"stats.directnic.com",
		"stats.hyperinzerce.cz",
		"statsie.com",
		"stats.mirrorfootball.co.uk",
		"stats.olark.com",
		"stats.suite101.com",
		"stats.surfaid.ihost.com",
		"stats.townnews.com",
		"stat.su",
		"stats.unwired-i.net",
		"stats.wordpress.com",
		"stats.x14.eu",
		"stat.tudou.com",
		"stat.webmedia.pl",
		"statxpress.com",
		"stat.zenon.net",
		"st-bo.kz",
		"steelhouse.com",
		"steelhousemedia.com",
		"stickyadstv.com",
		"stisa.org.cn",
		"stmaryslodgeno4.org",
		"stock5188.com",
		"stoneb.cn",
		"stopmeagency.free.fr",
		"stopmikelupica.com",
		"stralfors.home.pl",
		"strand-und-hund.de",
		"strangeduckfilms.com",
		"strategiccapitalalliance.com",
		"strikead.com",
		"strikeiron.com",
		"strmyy.com",
		"stroyeq.ru",
		"stycn.com",
		"suavalds.com",
		"subeihm.com",
		"subscribe.hearstmags.com",
		"successtest.co.kr",
		"sudanartists.org",
		"sugoicounter.com",
		"sujet-du-bac.com",
		"sukhshantisales.com",
		"sunggysus.com",
		"sunqtr.com",
		"supercell.net",
		"superclix.de",
		"superstats.com",
		"supertop100.com",
		"supertop.ru",
		"suptullog.com",
		"surfmusik-adserver.de",
		"sushischool.ru",
		"sushouspell.com",
		"svis.in",
		"swattradingco.name.qa",
		"sweepstakesandcontestsinfo.com",
		"swissadsolutions.com",
		"switchadhub.com",
		"switchads.com",
		"swordfishdc.com",
		"swt.sxhhyy.com",
		"swzhb.com",
		"sxhhyy.com",
		"sx.trhnt.com",
		"sykazt.com.cn",
		"sympation.com",
		"syndrome-de-poland.org",
		"szdamuzhi.com",
		"szesun.net",
		"sznaucer-figa.nd.e-wro.pl",
		"sznm.com.cn",
		"szzlzn.com",
		"t2t2.com",
		"t70123.com",
		"tablet.gutterhelment.net",
		"taboola.com",
		"tacoda.net",
		"tagular.com",
		"tahed.org",
		"tailsweep.com",
		"tailsweep.co.uk",
		"tailsweep.se",
		"taiwaninfogoods.com",
		"takru.com",
		"tallahasseeeyecare.com",
		"tamarer.com",
		"tampaiphonerepair.com",
		"tampamacrepair.com",
		"tangerinenet.biz",
		"tao0451.com",
		"tapad.com",
		"tapgen.com",
		"tapit.com",
		"tapjoyads.com",
		"tapjoy.com",
		"tapsense.com",
		"targad.de",
		"targetingnow.com",
		"targetnet.com",
		"targetpoint.com",
		"targetspot.com",
		"tatango.com",
		"tatsumi-sys.jp",
		"taximorganizasyon.com",
		"tbucki.eu",
		"tcads.net",
		"teatrorivellino.it",
		"techclicks.net",
		"techlivegen.com",
		"technosfera-nsk.ru",
		"teenrevenue.com",
		"teksograd.ru",
		"telephonie-voip.info",
		"teliad.de",
		"temnhankimloai.com",
		"templatemadness.com",
		"tenin58gaccel.rr.nu",
		"tentsf05luxfig.rr.nu",
		"tesorosdecancun.com",
		"test.com",
		"textads.biz",
		"textad.sexsearch.com",
		"textads.opera.com",
		"text-link-ads.com",
		"textlinks.com",
		"tezrsrc.gov.cn",
		"tfag.de",
		"tfpcmedia.org",
		"thdx08.com",
		"theadhost.com",
		"theads.me",
		"theblessedbee.co.uk",
		"thebugs.ws",
		"thecounter.com",
		"thelrein.com",
		"themodules.ru",
		"thenightshiftdiet.com",
		"thepainfreeformula.com",
		"theporkauthority.com",
		"therapistla.com",
		"therichkids.com",
		"therocnation.org",
		"thesalivan.com",
		"thesavvyunistudent.com",
		"the-wildbunch.net",
		"thinknear.com",
		"thinkupfront.com",
		"thirdrange.co.uk",
		"thomashobbs.com",
		"thomchotte.com",
		"thoosje.com",
		"thoukik.ru",
		"thrnt.com",
		"throne.thehelpbiz.com",
		"thruport.com",
		"thxhb.com",
		"tiantmall.com",
		"timedirect.ru",
		"t.insigit.com",
		"tinybar.com",
		"tinypic.info",
		"tizers.net",
		"tkxerw.com",
		"tlvmedia.com",
		"tmfilms.net",
		"tntclix.co.uk",
		"todacell.com",
		"today-newday.cn",
		"todaytime.net",
		"top100-images.rambler.ru",
		"top100.mafia.ru",
		"top123.ro",
		"top20.com",
		"top20free.com",
		"top66.ro",
		"top90.ro",
		"topapk.mobi",
		"topbarh.box.sk",
		"topblogarea.se",
		"topbucks.com",
		"top-casting-termine.de",
		"topforall.com",
		"topgamesites.net",
		"toplista.mw.hu",
		"toplistcity.com",
		"toplist.cz",
		"toplist.pornhost.com",
		"top.list.ru",
		"topmailersblog.com",
		"top.mail.ru",
		"topmmorpgsites.com",
		"topping.com.ua",
		"top.proext.com",
		"toprebates.com",
		"topsafelist.net",
		"topsearcher.com",
		"topsir.com",
		"top-site-list.com",
		"topsite.lv",
		"topsites.com.br",
		"topstats.com",
		"tork-aesthetics.de",
		"torreslimos.com",
		"torvaldscallthat.info",
		"totemcash.com",
		"tottaldomain.cn",
		"touchads.com",
		"touchclarity.com",
		"touchclarity.natwest.com",
		"tour.brazzers.com",
		"tourindia.in",
		"toursportsimage.com",
		"tpnads.com",
		"t.pusk.ru",
		"track.adform.net",
		"trackalyzer.com",
		"track.anchorfree.com",
		"tracker.icerocket.com",
		"tracker.marinsm.com",
		"trackersimulator.org",
		"track.gawker.com",
		"tracking101.com",
		"tracking.checkmygirlfriend.net",
		"tracking.crunchiemedia.com",
		"tracking.gajmp.com",
		"tracking.internetstores.de",
		"trackingsoft.com",
		"tracking.yourfilehost.com",
		"trackmysales.com",
		"tradeadexchange.com",
		"tradedoubler.com",
		"trademob.com",
		"trafdriver.com",
		"trafficadept.com",
		"trafficcdn.liveuniversenetwork.com",
		"traffic-exchange.com",
		"trafficfactory.biz",
		"trafficholder.com",
		"traffichunt.com",
		"trafficjunky.net",
		"trafficleader.com",
		"traffic.liveuniversenetwork.com",
		"trafficroup.com",
		"trafficsecrets.com",
		"trafficspaces.net",
		"trafficstrategies.com",
		"trafficswarm.com",
		"traffictrader.net",
		"trafficz.com",
		"trafficz.net",
		"traffiq.com",
		"traffok.cn",
		"trafic.ro",
		"transcontinental.com.qa",
		"transition.org.cn",
		"travis.bosscasinos.com",
		"trekblue.com",
		"trekdata.com",
		"tremorvideo.com",
		"trendcounter.com",
		"trenz.pl",
		"tr-gdz.ru",
		"trhunt.com",
		"tribalfusion.com",
		"triblabla.awasr.cn",
		"trix.net",
		"trouble.cachetinvestments.com",
		"truckersemanifest.com",
		"truehits1.gits.net.th",
		"truehits2.gits.net.th",
		"truehits.net",
		"trumpia.com",
		"tslongjian.com",
		"tsm.25u.com",
		"tsms-ad.tsms.com",
		"tstuhg.com",
		"ttb.lpcloudsvr302.com",
		"ttkdyw.com",
		"ttrtw.com",
		"ttu98fei.com",
		"ttu998d.com",
		"tubedspots.com",
		"tubemogul.com",
		"tube-xnxx.com",
		"tucsonhydraulics.com",
		"tu-ksa.com.mx",
		"tunatekstil.net",
		"turn.com",
		"turnkey-solutions.net",
		"tvandsportstreams.com",
		"tvas-a.pw",
		"tvas-c.pw",
		"tvmedion.pl",
		"tvmtracker.com",
		"twittad.com",
		"txtimpact.com",
		"txx521.com",
		"type.translatorvr.com",
		"tyroo.com",
		"tz.jiguangie.com",
		"uarating.com",
		"ubermedia.com",
		"uci.securesoft.info",
		"ufree.org",
		"uglyas.com",
		"ujvmzzwsxzrd3.com",
		"ukbanners.com",
		"ukkvdx.com",
		"ultimatepopupkiller.com",
		"ultramercial.com",
		"ultsearch.com",
		"unanimis.co.uk",
		"uni10.tk",
		"unionavenue.net",
		"unrulymedia.com",
		"untd.com",
		"up2disk.com",
		"updatedate.cn",
		"updated.com",
		"updatenowpro.com",
		"upperdarby26.com",
		"upsnap.com",
		"urbanityadnetwork.com",
		"urlcash.net",
		"urnsforpets.net",
		"u-ruraldoctor.com",
		"us.a1.yimg.com",
		"usa-jiaji.com",
		"usapromotravel.com",
		"usb-turn-table.co.uk",
		"user.fileserver.co.kr",
		"usergrid.com",
		"usmsad.tom.com",
		"utarget.co.uk",
		"utildata.co.kr",
		"utils.mediageneral.net",
		"utpsoxvninhi6.com",
		"uuu822.com",
		"uvatech.co.uk",
		"uxtop.ru",
		"uyqrwg.com",
		"v1.cnzz.com",
		"v1tj.jiguangie.com",
		"v2mlbrown.com",
		"v2mlyellow.com",
		"vakantiefoto.mobi",
		"valet-bablo.ru",
		"valetik.ru",
		"valhallarisingthemovie.co.uk",
		"validclick.com",
		"valuead.com",
		"valueclick.com",
		"valueclickmedia.com",
		"valuecommerce.com",
		"valuesponsor.com",
		"vasfagah.ru",
		"vasuarte.net",
		"vbit.co.in",
		"vbswzm.com",
		"vcbqxu.com",
		"vccd.cn",
		"vdopia.com",
		"vdownloads.ru",
		"vecherinka.com",
		"veille-referencement.com",
		"velti.com",
		"ventivmedia.com",
		"venturesindia.co.in",
		"verfer.com",
		"vericlick.com",
		"vertadnet.com",
		"veruta.com",
		"vervemobile.com",
		"vervewireless.com",
		"vfm.org.uk",
		"v-going.com.cn",
		"viartstudio.pl",
		"vibrantmedia.com",
		"vicirealestate.com",
		"victorydetailing.com",
		"videoegg.com",
		"video-stats.video.google.com",
		"view4cash.de",
		"viewpoint.com",
		"viewsfile.com",
		"viewwonder.com",
		"vilagnomad.com",
		"vimusic.net",
		"vip.dns-vip.net",
		"vipoptions.info",
		"vipprojects.cn",
		"vip-traffic.com",
		"virtual-pcb.com",
		"virus-help.us",
		"visistat.com",
		"visitbox.de",
		"visit.webhosting.yahoo.com",
		"visual-pagerank.fr",
		"visualrevenue.com",
		"vkfyqke.com.cn",
		"vnalex.tripod.com",
		"voicefive.com",
		"volpefurniture.com",
		"vpon.com",
		"vqlgli.com",
		"vra4.com",
		"vrot.stervapoimenialena.info",
		"vrs.cz",
		"vstart.net",
		"vs.tucows.com",
		"vungle.com",
		"w3i.com",
		"wads.webteh.com",
		"walesedu.com",
		"wangqiao365.com",
		"wangxiaorong.com",
		"wap.sxhhyy.com",
		"warface.sarhosting.ru",
		"warlog.info",
		"warlog.ru",
		"warp.ly",
		"watercircle.net",
		"watermanwebs.com",
		"wda.com",
		"wdads.sx.atl.publicus.com",
		"web2.deja.com",
		"webads.co.nz",
		"webads.nl",
		"webandcraft.com",
		"webangel.ru",
		"webcash.nl",
		"webcounter.cz",
		"webcounter.goweb.de",
		"webdesigning.name",
		"webgains.com",
		"web.informer.com",
		"webmaster-partnerprogramme24.de",
		"webmasterplan.com",
		"webmasterplan.de",
		"weborama.fr",
		"webpower.com",
		"webreseau.com",
		"webseoanalytics.com",
		"webservicesttt.ru",
		"websponsors.com",
		"webstat.channel4.com",
		"web-stat.com",
		"webstat.com",
		"webstat.net",
		"webstats4u.com",
		"webtrackerplus.com",
		"webtraffic.se",
		"webtraxx.de",
		"webtrendslive.com",
		"wee4wee.ws",
		"wegcash.com",
		"wenn88.com",
		"weqeweqqq2012.com",
		"werbeagentur-ruhrwerk.de",
		"werbung.meteoxpress.com",
		"wesleymedia.com",
		"westcountry.ru",
		"westdy.com",
		"westnorths.cn",
		"wetrack.it",
		"whaleads.com",
		"whenu.com",
		"whereapps.com",
		"whispa.com",
		"whoisonline.net",
		"wholesaletraffic.info",
		"widespace.com",
		"widgetbucks.com",
		"wiedemann.com",
		"wielkilukwarty.pl",
		"wikia-ads.wikia.com",
		"willdrey.com",
		"win345.cn",
		"winco-industries.com",
		"window.nixnet.cz",
		"winner.us",
		"winnipegdrugstore.com",
		"winstonchurchill.ca",
		"wintricksbanner.googlepages.com",
		"winupdate.phpnet.us",
		"witch-counter.de",
		"wittmangroup.com",
		"wittyvideos.com",
		"wlmarketing.com",
		"wlzjx.net",
		"wm5u.com",
		"w.mcdir.ru",
		"wmirk.ru",
		"wmljw.com",
		"wmtanhua.com",
		"woibt.com",
		"wonderlandads.com",
		"wondoads.de",
		"woodstonesubdivision.com",
		"woojeoung.com",
		"woopra.com",
		"woosungelec.com",
		"worldisonefamily.info",
		"worldwide-cash.net",
		"wowcpc.net",
		"wp.zontown.com",
		"writec.ca",
		"wsxhost.net",
		"wsxyx.com",
		"wtdpcb.com",
		"wtlive.com",
		"wtr1.ru",
		"wtracy.free.fr",
		"wushirongye.com",
		"ww1.hot-sextube.com",
		"ww31.hot-sextube.com",
		"ww3.way-of-fun.com",
		"wwgin.com",
		"wwniww.com",
		"wwttmm.com",
		"www.00game.net",
		"www.0797fdc.com.cn",
		"www.099499.com",
		"www11.kkuumn.com",
		"www12.688ooo.com",
		"www12.mmnidy.com",
		"www12.wwniww.com",
		"www131.mvnvpic.com",
		"www.13903825045.com",
		"www13.rtysus.com",
		"www146.lewwwz.com",
		"www14.rtyszz.com",
		"www154.173nvrenw.com",
		"www15.ktoooo.com",
		"www15.mmnidy.com",
		"www15.mnxgz.com",
		"www15.omrtw.com",
		"www16.51mogui.com",
		"www16.rtysus.com",
		"www16.wwttmm.com",
		"www172.lpwangzhan.com",
		"www1.777mnz.com",
		"www18.mm113.com",
		"www18.rtysus.com",
		"www18.rtyszz.com",
		"www19.71sise.com",
		"www19.777mnz.com",
		"www198.jixnbl.com",
		"www19.xioooo.com",
		"www1.gto-media.com",
		"www1.gxxmm.com",
		"www1.xise.cn",
		"www20.777mnz.com",
		"www209.xcxx518.com",
		"www20.ggaibb.com",
		"www20.hi7800.com",
		"www210.681luanlun.com",
		"www213.hdhd55.com",
		"www214.ttrtw.com",
		"www21.bolo100.com",
		"www21.qqxxdy.com",
		"www22.33lzmm.com",
		"www22.lbmm88.com",
		"www22.mmnidy.com",
		"www22.xyxsol.com",
		"www230.dm599.com",
		"www230.kkvmaj.com",
		"www238.killevo.com",
		"www238.lzxsw100.com",
		"www23.omrtw.com",
		"www23.qqmeise.com",
		"www240.dortxn.com",
		"www24.177momo.com",
		"www24.31qqww.com",
		"www244.lzxsw100.com",
		"www246.oliwei.com",
		"www24.fuqi3p.com",
		"www250.dm599.com",
		"www25.meenou.com",
		"www260.yinghuazhan.com",
		"www26.bjmn100.com",
		"www26.ktoooo.com",
		"www26.llbb88.com",
		"www26.mnxgz.com",
		"www26.rtysus.com",
		"www27.177momo.com",
		"www277.qshfwj.com",
		"www27.xyxsol.com",
		"www281.rentimeinvz.com",
		"www28.33lzmm.com",
		"www28.kkuumn.com",
		"www293.lewwwz.com",
		"www29.hjnvren.com",
		"www29.ltsetu.com",
		"www.2bbd.com",
		"www2.gxxmm.com",
		"www2.rtyszz.com",
		"www.2seo8.com",
		"www30.feieo.com",
		"www30.fuqi3p.com",
		"www31.177momo.com",
		"www31.dwttmm.com",
		"www32.rtyszz.com",
		"www3.32hy.com",
		"www33.688ooo.com",
		"www33.bjmn100.com",
		"www33.rtyszz.com",
		"www33.xzmnt.com",
		"www343.ohgooo.com",
		"www344.xoxmmm.com",
		"www346.tx5200.com",
		"www348.xcxx518.com",
		"www34.bjmn100.com",
		"www34.mmnidy.com",
		"www3.51hzmn.com",
		"www35.xzmnt.com",
		"www37.hjnvren.com",
		"www37.kkuumn.com",
		"www37.rtysus.com",
		"www37.yazouh.com",
		"www381.ddlczn.com",
		"www38.hi7800.com",
		"www38.mgscw.com",
		"www38.mimile8.com",
		"www39.71sise.com",
		"www39.gxxmm.com",
		"www39.ktoooo.com",
		"www3.wwniww.com",
		"www40.51mogui.com",
		"www40.688ooo.com",
		"www415.mxyyth.com",
		"www41.bolo100.com",
		"www41.dwttmm.com",
		"www41.xzmnt.com",
		"www42.meenou.com",
		"www42.rtyszz.com",
		"www43.173nvrenw.com",
		"www43.17sise.com",
		"www43.31qqww.com",
		"www43.6666mn.com",
		"www43.ggaibb.com",
		"www43.kkuumn.com",
		"www44.688ooo.com",
		"www44.ltsetu.com",
		"www453.dcabkl.com",
		"www45.6666mn.com",
		"www45.71sise.com",
		"www45.xi1111.com",
		"www46.bolo100.com",
		"www46.jijimn.com",
		"www48.177momo.com",
		"www48.omrtw.com",
		"www48.xioooo.com",
		"www49.ggaibb.com",
		"www49.mimile8.com",
		"www50.feieo.com",
		"www.5178424.com",
		"www.51xcedu.com",
		"www.51ysxs.com",
		"www.52209997.com",
		"www57.cbvccc.com",
		"www57.kannilulu.com",
		"www58.ovonnn.com",
		"www.58tpw.com",
		"www5.ggaibb.com",
		"www5.hi7800.com",
		"www5.wwttmm.com",
		"www5.xi1111.com",
		"www60.rimklh.com",
		"www.67www.com",
		"www.688ooo.com",
		"www6.mnxgz.com",
		"www6.omrtw.com",
		"www70.vcbqxu.com",
		"www730.mm6500.com",
		"www7.31mnn.com",
		"www74.rtkgvp.com",
		"www.75pp.com",
		"www7.6666mn.com",
		"www.78111.com",
		"www7.bolo100.com",
		"www7.jijimn.com",
		"www7.lbmm88.com",
		"www7.wwniww.com",
		"www83.lsxsccc.com",
		"www8.51hzmn.com",
		"www8.glam.com",
		"www.90888.com",
		"www94.xingggg.com",
		"www.ahwydljt.com",
		"www.alecctv.com",
		"www.amberlf.cn",
		"www.andrewmelchior.com",
		"www.anticarredodolomiti.com",
		"www.archtopmakers.com",
		"www.assculturaleincontri.it",
		"www-banner.chat.ru",
		"www.banner-link.com.br",
		"www.bivouac-iguana-sahara-merzouga.com",
		"www.blogonur.com",
		"www.caixapre.com.br",
		"www.cdhomexpo.cn",
		"www.cdlitong.com",
		"www.cellularbeton.it",
		"www.cfbrr.com",
		"www.chinafsw.cn",
		"www.china-jlt.com",
		"www.cibonline.org",
		"www.citystategarden.com",
		"www.cndownmb.com",
		"www.cnhdin.cn",
		"www.cn-server.com",
		"www.constructiveopinions.com",
		"www.defygravity.com",
		"www.dikesalerno.it",
		"www.dnps.com",
		"www.doctorvj.com",
		"www.elisaart.it",
		"www.exbaiduer.com",
		"www.fchabkirchen-frauenberg.de",
		"www.galileounaluna.com",
		"www.galliagroup.com",
		"www.gaohaiying.com",
		"www.gb206.com",
		"www.gdby.com.cn",
		"www.gdzjco.com",
		"www.gentedicartoonia.it",
		"www-google-analytics.l.google.com",
		"www.gzjjtz.com",
		"www.haphuongfoundation.net",
		"www.hdchd.org",
		"www.hengjia8.com",
		"www.hentelpower.com",
		"www.hi7800.com",
		"www.hryspap.cn",
		"www.huadianbeijing.com",
		"www.ictcmwellness.com",
		"www.infoaz.nl",
		"www.insideasiatravel.com",
		"www.ivysolutions.it",
		"www.kalandraka.pt",
		"www.kaplanindex.com",
		"www.ketaohua.com",
		"www.liquidacionessl.com",
		"www.lydaoyou.com",
		"www.maszcjc.com",
		"www.mimile8.com",
		"www.mm113.com",
		"www.money4exit.de",
		"www.myhongyuan.net",
		"www.nbyuxin.com",
		"www.newstudy.net",
		"www.ntdfbp.com",
		"www.p3322.com",
		"www.photo-ads.co.uk",
		"www.phpoutsourcingindia.com",
		"www.poesiadelsud.it",
		"www.ppwfb.com",
		"www.prjcode.com",
		"www.qgtjhw.com",
		"www.qhdast.com",
		"www.qqkabb.com",
		"www.riccardochinnici.it",
		"www.rsrly.com",
		"www.sailing3.com",
		"www.saunaundbad.de",
		"www.scoeyc.com",
		"www.softtube.cn",
		"www.soidc.com",
		"www.solo-juegos.com",
		"www.stkjw.net",
		"www.thomchotte.com",
		"www.thoosje.com",
		"www.tourindia.in",
		"www.unicaitaly.it",
		"www.uvatech.co.uk",
		"www.v3club.net",
		"www.valhallarisingthemovie.co.uk",
		"www.victory.com.pl",
		"www.vvpan.com",
		"www.webandcraft.com",
		"www.weigezhiyao.com",
		"www.wwgin.com",
		"www.xingzhanfengbao5.com",
		"www.xntk.net",
		"www.xtewx.com",
		"www.yc1234.com",
		"www.ydhyjy.com",
		"www.yserch.com",
		"wxfzkd.com",
		"wxjflab.com",
		"wxy.bnuep.com",
		"wyf003.cn",
		"wypromuj.nazwa.pl",
		"wzfmxlrrynnbekcqzu.com",
		"wzscales.com",
		"x6.yakiuchi.com",
		"x9qjl1o3yc.seojee.com",
		"xa58.cn",
		"xad.com",
		"xanjan.cn",
		"xap.ss.la",
		"xcdgfs.com",
		"xchange.ro",
		"xcl168.s37.jjisp.com",
		"xclicks.net",
		"xctzwsy.com",
		"xczys.com",
		"xdbwgs.com",
		"xertive.com",
		"xervio.technology",
		"xg4ken.com",
		"xgydq.com",
		"xhamstertube.com",
		"xhdz.net",
		"xhqsysp.com",
		"xi1111.com",
		"xiangni169.com",
		"xian.jztedu.com",
		"xianyicao.net",
		"xiao2012-01.yxdown.cn",
		"xiao2012-06.yxdown.cn",
		"xiao2012-15.yxdown.cn",
		"xiao2013-01.yxdown.cn",
		"xiao2013-03.yxdown.cn",
		"xiao2013-04.yxdown.cn",
		"xiao2013-05.yxdown.cn",
		"xiao2013-06.yxdown.cn",
		"xiao2013-07.yxdown.cn",
		"xiao2013-08.yxdown.cn",
		"xiao2013-10.yxdown.cn",
		"xiao2013-11.yxdown.cn",
		"xiao2013-12.yxdown.cn",
		"xiao2013-13.yxdown.cn",
		"xiao2013-14.yxdown.cn",
		"xiao2013-15.yxdown.cn",
		"xiao2013-17.yxdown.cn",
		"xiaocen.com",
		"xiaommn.com",
		"xiazai2.net",
		"xiazai.dns-vip.net",
		"xiazhai.xiaocen.com",
		"xiguasew.com",
		"xigushan.com",
		"xigushan.net",
		"xingqibaile.com",
		"xingsi.com",
		"xingyunjiaren.com",
		"xingzhanfengbao5.com",
		"xinhaoxuan.com",
		"xinhuawindows.com",
		"xin-lian.cn",
		"xinweico.net",
		"xinxinbaidu.com.cn",
		"xinyangmeiye.com",
		"xinyitaoci.com",
		"xioooo.com",
		"xiti.com",
		"xiugaiba.com",
		"xius.com",
		"xixiasedy.com",
		"xixile361.com",
		"xjgyb.com",
		"xmtkj.com",
		"xn--80aaagge2acs2agf3bgi.xn--p1ai",
		"xn--orw0a8690a.com",
		"xoads.com",
		"xobjzmhopjbboqkmc.com",
		"xoxmmm.com",
		"xplusone.com",
		"xponsor.com",
		"xpresms.com",
		"xpxp06.com",
		"xpxp36.com",
		"xpxp48.com",
		"xpxp53.com",
		"xpxp74.com",
		"xq1.net",
		"xqqd.net",
		"xrea.com",
		"xr.flyboytees.com",
		"xrs56.com",
		"xsd6.com",
		"xsso.anbtr.com",
		"xtendmedia.com",
		"xtewx.com",
		"xtqizu.com",
		"x-traceur.com",
		"xtremetop100.com",
		"xtxgsx.com",
		"xuelisz.com",
		"xuemeilu.com",
		"xuexingmm.com",
		"xx52200.com",
		"xxi.ss.la",
		"xxooyx.com",
		"xxxcounter.com",
		"xxxmyself.com",
		"xxxporno18.ru",
		"xy7elite.com",
		"xy-cs.net",
		"xyguilin.com",
		"xyhpkj.com",
		"xymlhxg.com",
		"xyxsol.com",
		"xyybaike.com",
		"xz9u.com",
		"xzheli.com",
		"xz.hkfg.net",
		"xzmnt.com",
		"xzsk.com",
		"xzz.goodoboy.com",
		"y73shop.com",
		"y822.com",
		"yab-adimages.s3.amazonaws.com",
		"yabuka.com",
		"yadro.ru",
		"ya-googl.ws",
		"y.ai",
		"yanagi.co.kr",
		"yangqifoods.com",
		"yangzhou.c-zs.com",
		"yannick.delamarre.free.fr",
		"yantushi.cn",
		"yaxay.com",
		"yazhoutupianwang.com",
		"yazouh.com",
		"ybjch.cn",
		"ybrantdigital.com",
		"yc1234.com",
		"yclydq.com",
		"ycshiweitian.com",
		"ycwlky.com",
		"ycyns.com",
		"yd315.com",
		"ydworld.com",
		"yegushi.com",
		"yembonegroup.com",
		"ye-mo.org.il",
		"yeniyuzyillions.org",
		"yes1899.com",
		"yes4biz.net",
		"yesads.com",
		"yesadvertising.com",
		"yeshigongzhu.com",
		"yesteam.org.in",
		"yfcarh.com",
		"yfdiet.com",
		"yfvnve.com",
		"yhjlhb.com",
		"y.ibsys.com",
		"yiduaner.cn",
		"yieldads.com",
		"yieldlab.net",
		"yieldmanager.com",
		"yieldmanager.net",
		"yieldtraffic.com",
		"yihaotui.com",
		"yiheng.jztedu.com",
		"yinpingshan.net",
		"yinputech.com",
		"yinyuanhotel.net",
		"yixingim.com",
		"ykkg.com",
		"ylcoffeetea.com",
		"ylmqjz.com",
		"ylprwb.com",
		"ynrenai.net",
		"ynxp.co",
		"yoc.mobi",
		"yoc-performance.com",
		"yoggrt.com",
		"yorkstrike.on.nimp.org",
		"youaskedthedomain.cn",
		"youknownow.ru",
		"youkuedu.com",
		"yousewan.com",
		"youthfire.com",
		"youthsprout.com",
		"yoyoykamphora.com",
		"ypschool.cn",
		"yqybjyw.com",
		"yrnvau.com",
		"ysbbcrypsc.com",
		"yserch.com",
		"ysjtly.com",
		"ytdhshoutidai.com",
		"yttestsite.com",
		"ytx360.com",
		"yuanjiaomm.com",
		"yuankouvip.com",
		"yuejinjx.com",
		"yueqi360.com",
		"yuilop.com",
		"yume.com",
		"yuminhong.blog.neworiental.org",
		"yusungtech.co.kr",
		"yuxiwine.com",
		"yuyu.com",
		"yxb77.com",
		"yxcqhb.com",
		"yxhlv.com",
		"yxhxtc.net",
		"yxshengda.com",
		"yxxzzt.com",
		"yxzyjx.net",
		"yyjgift.com",
		"yysscc.com",
		"yz-sl.cn",
		"yzunited.com",
		"z5x.net",
		"zagga.in",
		"zangocash.com",
		"zango.com",
		"zanox-affiliate.de",
		"zanox.com",
		"zantracker.com",
		"zara11.com",
		"zavidovodom.com",
		"zbjpsy.com",
		"zbzppbwqmm.biz",
		"zchon.net",
		"zde-affinity.edgecaching.net",
		"zdesestvareznezahodi.com",
		"zdlceq.com",
		"zedo.com",
		"zeepmedia.com",
		"zekert.com",
		"zencudo.co.uk",
		"zenitchampion.cn",
		"zenkreka.com",
		"zenzuu.com",
		"zeroclan.net",
		"zeusclicks.com",
		"zeus.developershed.com",
		"zfb2015.com",
		"zgdjc.com",
		"zgfhl.com",
		"zh18.net",
		"zhaopian.de",
		"zhenzhongmuye.com",
		"zhidao.yxad.com",
		"zhiher.com",
		"zhijufang.com",
		"zhizhishe.com",
		"zhongguociwang.com",
		"zhonghe-zg.com",
		"zhongpandz.com",
		"zhongyilunwen.com",
		"zhs389.com",
		"zief.pl",
		"ziheyuan.com",
		"zimeks.com.mk",
		"zintext.com",
		"zixunxiu.com",
		"zjhnyz.com",
		"zjhuashi.net",
		"zjknx.cn",
		"zjkxunda.com",
		"zjylk.com",
		"zmedia.com",
		"zmt100.com",
		"zndxa.com",
		"zoetekroon.nl",
		"zotasinc.com",
		"zoygroup.com",
		"zpfrak.com",
		"zqmdm.com",
		"zs.hniuzsjy.cn",
		"zsmisaki.com",
		"zsw.jsyccnxq.com",
		"ztgy.com",
		"ztkmne.com",
		"zum.mudmaggot.com",
		"zumobi.com",
		"zvezda-group.ru",
		"zw52.ru",
		"zwgoca.com",
		"zyjyyy.com",
		"zzdsfy.com",
		"zzha.net",
		"zzhtv.com",
		"zzjfl.net",
		"zzjgjjh.com",
		"zzmyw.com",
		"zzpxw.cn",
		"zzshw.net",
		"zztxdown.com"
                };

    for (String sites : blockedSites) {
         for (String site : sites.split(" ")) {
            if (host.toLowerCase().endsWith(site.toLowerCase())) {
                return true; 
                }
         }
    }
    return false;
    }

        @Override
        public WebResourceResponse shouldInterceptRequest(WebView view,
                String url) {


            boolean useMostVisited = BrowserSettings.getInstance().useMostVisitedHomepage();
            Uri uri = Uri.parse(url);

            if (useMostVisited && url.startsWith("content://")) {
                if (HomeProvider.AUTHORITY.equals(uri.getAuthority())) {
                    try {
                        InputStream ins = mContext.getApplicationContext().getContentResolver()
                            .openInputStream(Uri.parse(url + "/home"));
                        return new WebResourceResponse("text/html", "utf-8", ins);
                    } catch (java.io.FileNotFoundException e) {
                    }
                }
            }
            if (uri.getScheme().toLowerCase().equals("file")) {
                File file = new File(uri.getPath());
                try {
                    if (file.getCanonicalPath().startsWith(
                            mContext.getApplicationContext().getApplicationInfo().dataDir)) {
                        return new WebResourceResponse("text/html","UTF-8",
                                new ByteArrayInputStream(RESTRICTED.getBytes("UTF-8")));
                    }
                } catch (Exception ex) {
                    Log.e(LOGTAG, "Bad canonical path" + ex.toString());
                    try {
                        return new WebResourceResponse("text/html","UTF-8",
                                new ByteArrayInputStream(RESTRICTED.getBytes("UTF-8")));
                    } catch (java.io.UnsupportedEncodingException e) {
                    }
                }
            }
            
            if (url.equals("browser:incognito")||url.startsWith("about")||!url.startsWith("http")){
                // just do nothing
                Log.v(LOGTAG, "Detected incognito or about or data:// app store etc");
                }
                else if (url.startsWith("http")){
                    if (isBlockedSite(url)) {
                    Uri uri2 = Uri.parse(url);
                    return new WebResourceResponse("text/plain", "utf-8", 
                    new ByteArrayInputStream(("[The following URL was blocked " + uri2.getHost() + "]").getBytes()));
                    }
                }


            WebResourceResponse res = HomeProvider.shouldInterceptRequest(
                    mContext, url);
            return res;
        }


        @Override
        public boolean shouldOverrideKeyEvent(WebView view, KeyEvent event) {
            if (!mInForeground) {
                return false;
            }
            return mWebViewController.shouldOverrideKeyEvent(event);
        }

        @Override
        public void onUnhandledKeyEvent(WebView view, KeyEvent event) {
            if (!mInForeground) {
                return;
            }
            if (!mWebViewController.onUnhandledKeyEvent(event)) {
                super.onUnhandledKeyEvent(view, event);
            }
        }

        @Override
        public void onReceivedLoginRequest(WebView view, String realm,
                String account, String args) {
            new DeviceAccountLogin(mWebViewController.getActivity(), view, Tab.this, mWebViewController)
                    .handleLogin(realm, account, args);
        }

    };

    private void syncCurrentState(WebView view, String url) {
        // Sync state (in case of stop/timeout)
        mCurrentState.mUrl = view.getUrl();
        if (mCurrentState.mUrl == null) {
            mCurrentState.mUrl = "";
        }
        mCurrentState.mOriginalUrl = view.getOriginalUrl();
        mCurrentState.mTitle = view.getTitle();
        mCurrentState.mFavicon = view.getFavicon();
        if (!URLUtil.isHttpsUrl(mCurrentState.mUrl)) {
            // In case we stop when loading an HTTPS page from an HTTP page
            // but before a provisional load occurred
            mCurrentState.mSecurityState = SecurityState.SECURITY_STATE_NOT_SECURE;
            mCurrentState.mSslCertificateError = null;
        }
        mCurrentState.mIncognito = view.isPrivateBrowsingEnabled();
    }

    // Called by DeviceAccountLogin when the Tab needs to have the auto-login UI
    // displayed.
    void setDeviceAccountLogin(DeviceAccountLogin login) {
        mDeviceAccountLogin = login;
    }

    // Returns non-null if the title bar should display the auto-login UI.
    DeviceAccountLogin getDeviceAccountLogin() {
        return mDeviceAccountLogin;
    }

    // -------------------------------------------------------------------------
    // WebChromeClient implementation for the main WebView
    // -------------------------------------------------------------------------

    private final WebChromeClient mWebChromeClient = new WebChromeClient() {
        // Helper method to create a new tab or sub window.
        private void createWindow(final boolean dialog, final Message msg) {
            WebView.WebViewTransport transport =
                    (WebView.WebViewTransport) msg.obj;
            if (dialog) {
                createSubWindow();
                mWebViewController.attachSubWindow(Tab.this);
                transport.setWebView(mSubView);
            } else {
                final Tab newTab = mWebViewController.openTab(null,
                        Tab.this, true, true);
                transport.setWebView(newTab.getWebView());
            }
            msg.sendToTarget();
        }

        @Override
        public boolean onCreateWindow(WebView view, final boolean dialog,
                final boolean userGesture, final Message resultMsg) {
            // only allow new window or sub window for the foreground case
            if (!mInForeground) {
                return false;
            }
            // Short-circuit if we can't create any more tabs or sub windows.
            if (dialog && mSubView != null) {
                new AlertDialog.Builder(mContext)
                        .setTitle(R.string.too_many_subwindows_dialog_title)
                        .setIconAttribute(android.R.attr.alertDialogIcon)
                        .setMessage(R.string.too_many_subwindows_dialog_message)
                        .setPositiveButton(R.string.ok, null)
                        .show();
                return false;
            } else if (!mWebViewController.getTabControl().canCreateNewTab()) {
                new AlertDialog.Builder(mContext)
                        .setTitle(R.string.too_many_windows_dialog_title)
                        .setIconAttribute(android.R.attr.alertDialogIcon)
                        .setMessage(R.string.too_many_windows_dialog_message)
                        .setPositiveButton(R.string.ok, null)
                        .show();
                return false;
            }

            // Short-circuit if this was a user gesture.
            if (userGesture) {
                createWindow(dialog, resultMsg);
                return true;
            }

            // Allow the popup and create the appropriate window.
            final AlertDialog.OnClickListener allowListener =
                    new AlertDialog.OnClickListener() {
                        public void onClick(DialogInterface d,
                                int which) {
                            createWindow(dialog, resultMsg);
                        }
                    };

            // Block the popup by returning a null WebView.
            final AlertDialog.OnClickListener blockListener =
                    new AlertDialog.OnClickListener() {
                        public void onClick(DialogInterface d, int which) {
                            resultMsg.sendToTarget();
                        }
                    };

            // Build a confirmation dialog to display to the user.
            final AlertDialog d =
                    new AlertDialog.Builder(mContext)
                    .setIconAttribute(android.R.attr.alertDialogIcon)
                    .setMessage(R.string.popup_window_attempt)
                    .setPositiveButton(R.string.allow, allowListener)
                    .setNegativeButton(R.string.block, blockListener)
                    .setCancelable(false)
                    .create();

            // Show the confirmation dialog.
            d.show();
            return true;
        }

        @Override
        public void onRequestFocus(WebView view) {
            if (!mInForeground) {
                mWebViewController.switchToTab(Tab.this);
            }
        }

        @Override
        public void onCloseWindow(WebView window) {
            if (mParent != null) {
                // JavaScript can only close popup window.
                if (mInForeground) {
                    mWebViewController.switchToTab(mParent);
                }
                mWebViewController.closeTab(Tab.this);
            }
        }

        @Override
        public boolean onJsAlert(WebView view, String url, String message,
                JsResult result) {
            mWebViewController.getTabControl().setActiveTab(Tab.this);
            return false;
        }

        @Override
        public boolean onJsConfirm(WebView view, String url, String message,
                JsResult result) {
            mWebViewController.getTabControl().setActiveTab(Tab.this);
            return false;
        }

        @Override
        public boolean onJsPrompt(WebView view, String url, String message,
                String defaultValue, JsPromptResult result) {
            mWebViewController.getTabControl().setActiveTab(Tab.this);
            return false;
        }

        @Override
        public void onProgressChanged(WebView view, int newProgress) {
            mPageLoadProgress = newProgress;
            if (newProgress == 100) {
                mInPageLoad = false;
            }
            mWebViewController.onProgressChanged(Tab.this);
            if (mUpdateThumbnail && newProgress == 100) {
                mUpdateThumbnail = false;
            }
        }

        @Override
        public void onReceivedTitle(WebView view, final String title) {
            mCurrentState.mTitle = title;
            mWebViewController.onReceivedTitle(Tab.this, title);
        }

        @Override
        public void onReceivedIcon(WebView view, Bitmap icon) {
            mCurrentState.mFavicon = icon;
            mWebViewController.onFavicon(Tab.this, view, icon);
        }

        @Override
        public void onReceivedTouchIconUrl(WebView view, String url,
                boolean precomposed) {
            final ContentResolver cr = mContext.getContentResolver();
            // Let precomposed icons take precedence over non-composed
            // icons.
            if (precomposed && mTouchIconLoader != null) {
                mTouchIconLoader.cancel(false);
                mTouchIconLoader = null;
            }
            // Have only one async task at a time.
            if (mTouchIconLoader == null) {
                mTouchIconLoader = new DownloadTouchIcon(Tab.this, cr, view);
                mTouchIconLoader.execute(url);
            }
        }

        @Override
        public void onShowCustomView(View view,
                WebChromeClient.CustomViewCallback callback) {
            Activity activity = mWebViewController.getActivity();
            if (activity != null) {
                onShowCustomView(view, activity.getRequestedOrientation(), callback);
            }
        }

        @Override
        public void onShowCustomView(View view, int requestedOrientation,
                WebChromeClient.CustomViewCallback callback) {
            if (mInForeground) mWebViewController.showCustomView(Tab.this, view,
                    requestedOrientation, callback);
        }

        @Override
        public void onHideCustomView() {
            if (mInForeground) mWebViewController.hideCustomView();
        }

        /**
         * The origin has exceeded its database quota.
         * @param url the URL that exceeded the quota
         * @param databaseIdentifier the identifier of the database on which the
         *            transaction that caused the quota overflow was run
         * @param currentQuota the current quota for the origin.
         * @param estimatedSize the estimated size of the database.
         * @param totalUsedQuota is the sum of all origins' quota.
         * @param quotaUpdater The callback to run when a decision to allow or
         *            deny quota has been made. Don't forget to call this!
         */
        @Override
        public void onExceededDatabaseQuota(String url,
            String databaseIdentifier, long currentQuota, long estimatedSize,
            long totalUsedQuota, WebStorage.QuotaUpdater quotaUpdater) {
            mSettings.getWebStorageSizeManager()
                    .onExceededDatabaseQuota(url, databaseIdentifier,
                            currentQuota, estimatedSize, totalUsedQuota,
                            quotaUpdater);
        }

        /**
         * The Application Cache has exceeded its max size.
         * @param spaceNeeded is the amount of disk space that would be needed
         *            in order for the last appcache operation to succeed.
         * @param totalUsedQuota is the sum of all origins' quota.
         * @param quotaUpdater A callback to inform the WebCore thread that a
         *            new app cache size is available. This callback must always
         *            be executed at some point to ensure that the sleeping
         *            WebCore thread is woken up.
         */
        @Override
        public void onReachedMaxAppCacheSize(long spaceNeeded,
                long totalUsedQuota, WebStorage.QuotaUpdater quotaUpdater) {
            mSettings.getWebStorageSizeManager()
                    .onReachedMaxAppCacheSize(spaceNeeded, totalUsedQuota,
                            quotaUpdater);
        }

        /**
         * Instructs the browser to show a prompt to ask the user to set the
         * Geolocation permission state for the specified origin.
         * @param origin The origin for which Geolocation permissions are
         *     requested.
         * @param callback The callback to call once the user has set the
         *     Geolocation permission state.
         */
        @Override
        public void onGeolocationPermissionsShowPrompt(String origin,
                GeolocationPermissions.Callback callback) {
            if (mInForeground) {
                getGeolocationPermissionsPrompt().show(origin, callback);
            }
        }

        /**
         * Instructs the browser to hide the Geolocation permissions prompt.
         */
        @Override
        public void onGeolocationPermissionsHidePrompt() {
            if (mInForeground && mGeolocationPermissionsPrompt != null) {
                mGeolocationPermissionsPrompt.hide();
            }
        }

        @Override
        public void onPermissionRequest(PermissionRequest request) {
            if (!mInForeground) return;
            getPermissionsPrompt().show(request);
        }

        @Override
        public void onPermissionRequestCanceled(PermissionRequest request) {
            if (mInForeground && mPermissionsPrompt != null) {
                mPermissionsPrompt.hide();
            }
        }

        /* Adds a JavaScript error message to the system log and if the JS
         * console is enabled in the about:debug options, to that console
         * also.
         * @param consoleMessage the message object.
         */
        @Override
        public boolean onConsoleMessage(ConsoleMessage consoleMessage) {
            if (mInForeground) {
                // call getErrorConsole(true) so it will create one if needed
                ErrorConsoleView errorConsole = getErrorConsole(true);
                errorConsole.addErrorMessage(consoleMessage);
                if (mWebViewController.shouldShowErrorConsole()
                        && errorConsole.getShowState() !=
                            ErrorConsoleView.SHOW_MAXIMIZED) {
                    errorConsole.showConsole(ErrorConsoleView.SHOW_MINIMIZED);
                }
            }

            // Don't log console messages in private browsing mode
            if (isPrivateBrowsingEnabled()) return true;

            String message = "Console: " + consoleMessage.message() + " "
                    + consoleMessage.sourceId() +  ":"
                    + consoleMessage.lineNumber();

            switch (consoleMessage.messageLevel()) {
                case TIP:
                    Log.v(CONSOLE_LOGTAG, message);
                    break;
                case LOG:
                    Log.i(CONSOLE_LOGTAG, message);
                    break;
                case WARNING:
                    Log.w(CONSOLE_LOGTAG, message);
                    break;
                case ERROR:
                    Log.e(CONSOLE_LOGTAG, message);
                    break;
                case DEBUG:
                    Log.d(CONSOLE_LOGTAG, message);
                    break;
            }

            return true;
        }

        /**
         * Ask the browser for an icon to represent a <video> element.
         * This icon will be used if the Web page did not specify a poster attribute.
         * @return Bitmap The icon or null if no such icon is available.
         */
        @Override
        public Bitmap getDefaultVideoPoster() {
            if (mInForeground) {
                return mWebViewController.getDefaultVideoPoster();
            }
            return null;
        }

        /**
         * Ask the host application for a custom progress view to show while
         * a <video> is loading.
         * @return View The progress view.
         */
        @Override
        public View getVideoLoadingProgressView() {
            if (mInForeground) {
                return mWebViewController.getVideoLoadingProgressView();
            }
            return null;
        }

        @Override
        public boolean onShowFileChooser(WebView webView, ValueCallback<Uri[]> callback,
            FileChooserParams params) {
            if (mInForeground) {
                mWebViewController.showFileChooser(callback, params);
                return true;
            } else {
                return false;
            }
        }

        /**
         * Deliver a list of already-visited URLs
         */
        @Override
        public void getVisitedHistory(final ValueCallback<String[]> callback) {
            if (isPrivateBrowsingEnabled()) {
                callback.onReceiveValue(new String[0]);
            } else {
                mWebViewController.getVisitedHistory(callback);
            }
        }

    };

    // -------------------------------------------------------------------------
    // WebViewClient implementation for the sub window
    // -------------------------------------------------------------------------

    // Subclass of WebViewClient used in subwindows to notify the main
    // WebViewClient of certain WebView activities.
    private static class SubWindowClient extends WebViewClient {
        // The main WebViewClient.
        private final WebViewClient mClient;
        private final WebViewController mController;

        SubWindowClient(WebViewClient client, WebViewController controller) {
            mClient = client;
            mController = controller;
        }
        @Override
        public void onPageStarted(WebView view, String url, Bitmap favicon) {
            // Unlike the others, do not call mClient's version, which would
            // change the progress bar.  However, we do want to remove the
            // find or select dialog.
            mController.endActionMode();
        }
        @Override
        public void doUpdateVisitedHistory(WebView view, String url,
                boolean isReload) {
            mClient.doUpdateVisitedHistory(view, url, isReload);
        }
        @Override
        public boolean shouldOverrideUrlLoading(WebView view, String url) {
            return mClient.shouldOverrideUrlLoading(view, url);
        }
        @Override
        public void onReceivedSslError(WebView view, SslErrorHandler handler,
                SslError error) {
            mClient.onReceivedSslError(view, handler, error);
        }
        @Override
        public void onReceivedClientCertRequest(WebView view, ClientCertRequest request) {
            mClient.onReceivedClientCertRequest(view, request);
        }
        @Override
        public void onReceivedHttpAuthRequest(WebView view,
                HttpAuthHandler handler, String host, String realm) {
            mClient.onReceivedHttpAuthRequest(view, handler, host, realm);
        }
        @Override
        public void onFormResubmission(WebView view, Message dontResend,
                Message resend) {
            mClient.onFormResubmission(view, dontResend, resend);
        }
        @Override
        public void onReceivedError(WebView view, int errorCode,
                String description, String failingUrl) {
            mClient.onReceivedError(view, errorCode, description, failingUrl);
        }
        @Override
        public boolean shouldOverrideKeyEvent(WebView view,
                android.view.KeyEvent event) {
            return mClient.shouldOverrideKeyEvent(view, event);
        }
        @Override
        public void onUnhandledKeyEvent(WebView view,
                android.view.KeyEvent event) {
            mClient.onUnhandledKeyEvent(view, event);
        }
    }

    // -------------------------------------------------------------------------
    // WebChromeClient implementation for the sub window
    // -------------------------------------------------------------------------

    private class SubWindowChromeClient extends WebChromeClient {
        // The main WebChromeClient.
        private final WebChromeClient mClient;

        SubWindowChromeClient(WebChromeClient client) {
            mClient = client;
        }
        @Override
        public void onProgressChanged(WebView view, int newProgress) {
            mClient.onProgressChanged(view, newProgress);
        }
        @Override
        public boolean onCreateWindow(WebView view, boolean dialog,
                boolean userGesture, android.os.Message resultMsg) {
            return mClient.onCreateWindow(view, dialog, userGesture, resultMsg);
        }
        @Override
        public void onCloseWindow(WebView window) {
            if (window != mSubView) {
                Log.e(LOGTAG, "Can't close the window");
            }
            mWebViewController.dismissSubWindow(Tab.this);
        }
    }

    // -------------------------------------------------------------------------

    // Construct a new tab
    Tab(WebViewController wvcontroller, WebView w) {
        this(wvcontroller, w, null);
    }

    Tab(WebViewController wvcontroller, Bundle state) {
        this(wvcontroller, null, state);
    }

    Tab(WebViewController wvcontroller, WebView w, Bundle state) {
        mWebViewController = wvcontroller;
        mContext = mWebViewController.getContext();
        mSettings = BrowserSettings.getInstance();
        mDataController = DataController.getInstance(mContext);
        mCurrentState = new PageState(mContext, w != null
                ? w.isPrivateBrowsingEnabled() : false);
        mInPageLoad = false;
        mInForeground = false;

        mDownloadListener = new BrowserDownloadListener() {
            public void onDownloadStart(String url, String userAgent,
                    String contentDisposition, String mimetype, String referer,
                    long contentLength) {
                mWebViewController.onDownloadStart(Tab.this, url, userAgent, contentDisposition,
                        mimetype, referer, contentLength);
            }
        };
        mWebBackForwardListClient = new WebBackForwardListClient() {
            @Override
            public void onNewHistoryItem(WebHistoryItem item) {
                if (mClearHistoryUrlPattern != null) {
                    boolean match =
                        mClearHistoryUrlPattern.matcher(item.getOriginalUrl()).matches();
                    if (LOGD_ENABLED) {
                        Log.d(LOGTAG, "onNewHistoryItem: match=" + match + "\n\t"
                                + item.getUrl() + "\n\t"
                                + mClearHistoryUrlPattern);
                    }
                    if (match) {
                        if (mMainView != null) {
                            mMainView.clearHistory();
                        }
                    }
                    mClearHistoryUrlPattern = null;
                }
            }
        };

        mCaptureWidth = mContext.getResources().getDimensionPixelSize(
                R.dimen.tab_thumbnail_width);
        mCaptureHeight = mContext.getResources().getDimensionPixelSize(
                R.dimen.tab_thumbnail_height);
        updateShouldCaptureThumbnails();
        restoreState(state);
        if (getId() == -1) {
            mId = TabControl.getNextId();
        }
        setWebView(w);
        mHandler = new Handler() {
            @Override
            public void handleMessage(Message m) {
                switch (m.what) {
                case MSG_CAPTURE:
                    capture();
                    break;
                }
            }
        };
    }

    public boolean shouldUpdateThumbnail() {
        return mUpdateThumbnail;
    }

    /**
     * This is used to get a new ID when the tab has been preloaded, before it is displayed and
     * added to TabControl. Preloaded tabs can be created before restoreInstanceState, leading
     * to overlapping IDs between the preloaded and restored tabs.
     */
    public void refreshIdAfterPreload() {
        mId = TabControl.getNextId();
    }

    public void updateShouldCaptureThumbnails() {
        if (mWebViewController.shouldCaptureThumbnails()) {
            synchronized (Tab.this) {
                if (mCapture == null) {
                    mCapture = Bitmap.createBitmap(mCaptureWidth, mCaptureHeight,
                            Bitmap.Config.RGB_565);
                    mCapture.eraseColor(Color.WHITE);
                    if (mInForeground) {
                        postCapture();
                    }
                }
            }
        } else {
            synchronized (Tab.this) {
                mCapture = null;
                deleteThumbnail();
            }
        }
    }

    public void setController(WebViewController ctl) {
        mWebViewController = ctl;
        updateShouldCaptureThumbnails();
    }

    public long getId() {
        return mId;
    }

    void setWebView(WebView w) {
        setWebView(w, true);
    }

    /**
     * Sets the WebView for this tab, correctly removing the old WebView from
     * the container view.
     */
    void setWebView(WebView w, boolean restore) {
        if (mMainView == w) {
            return;
        }

        // If the WebView is changing, the page will be reloaded, so any ongoing
        // Geolocation permission requests are void.
        if (mGeolocationPermissionsPrompt != null) {
            mGeolocationPermissionsPrompt.hide();
        }

        if (mPermissionsPrompt != null) {
            mPermissionsPrompt.hide();
        }

        mWebViewController.onSetWebView(this, w);

        if (mMainView != null) {
            mMainView.setPictureListener(null);
            if (w != null) {
                syncCurrentState(w, null);
            } else {
                mCurrentState = new PageState(mContext, false);
            }
        }
        // set the new one
        mMainView = w;
        // attach the WebViewClient, WebChromeClient and DownloadListener
        if (mMainView != null) {
            mMainView.setWebViewClient(mWebViewClient);
            mMainView.setWebChromeClient(mWebChromeClient);
            // Attach DownloadManager so that downloads can start in an active
            // or a non-active window. This can happen when going to a site that
            // does a redirect after a period of time. The user could have
            // switched to another tab while waiting for the download to start.
            mMainView.setDownloadListener(mDownloadListener);
            TabControl tc = mWebViewController.getTabControl();
            if (tc != null && tc.getOnThumbnailUpdatedListener() != null) {
                mMainView.setPictureListener(this);
            }
            if (restore && (mSavedState != null)) {
                restoreUserAgent();
                WebBackForwardList restoredState
                        = mMainView.restoreState(mSavedState);
                if (restoredState == null || restoredState.getSize() == 0) {
                    Log.w(LOGTAG, "Failed to restore WebView state!");
                    loadUrl(mCurrentState.mOriginalUrl, null);
                }
                mSavedState = null;
            }
        }
    }

    /**
     * Destroy the tab's main WebView and subWindow if any
     */
    void destroy() {
        if (mMainView != null) {
            dismissSubWindow();
            // save the WebView to call destroy() after detach it from the tab
            WebView webView = mMainView;
            setWebView(null);
            webView.destroy();
        }
    }

    /**
     * Remove the tab from the parent
     */
    void removeFromTree() {
        // detach the children
        if (mChildren != null) {
            for(Tab t : mChildren) {
                t.setParent(null);
            }
        }
        // remove itself from the parent list
        if (mParent != null) {
            mParent.mChildren.remove(this);
        }
        deleteThumbnail();
    }

    /**
     * Create a new subwindow unless a subwindow already exists.
     * @return True if a new subwindow was created. False if one already exists.
     */
    boolean createSubWindow() {
        if (mSubView == null) {
            mWebViewController.createSubWindow(this);
            mSubView.setWebViewClient(new SubWindowClient(mWebViewClient,
                    mWebViewController));
            mSubView.setWebChromeClient(new SubWindowChromeClient(
                    mWebChromeClient));
            // Set a different DownloadListener for the mSubView, since it will
            // just need to dismiss the mSubView, rather than close the Tab
            mSubView.setDownloadListener(new BrowserDownloadListener() {
                public void onDownloadStart(String url, String userAgent,
                        String contentDisposition, String mimetype, String referer,
                        long contentLength) {
                    mWebViewController.onDownloadStart(Tab.this, url, userAgent,
                            contentDisposition, mimetype, referer, contentLength);
                    if (mSubView.copyBackForwardList().getSize() == 0) {
                        // This subwindow was opened for the sole purpose of
                        // downloading a file. Remove it.
                        mWebViewController.dismissSubWindow(Tab.this);
                    }
                }
            });
            mSubView.setOnCreateContextMenuListener(mWebViewController.getActivity());
            return true;
        }
        return false;
    }

    /**
     * Dismiss the subWindow for the tab.
     */
    void dismissSubWindow() {
        if (mSubView != null) {
            mWebViewController.endActionMode();
            mSubView.destroy();
            mSubView = null;
            mSubViewContainer = null;
        }
    }


    /**
     * Set the parent tab of this tab.
     */
    void setParent(Tab parent) {
        if (parent == this) {
            throw new IllegalStateException("Cannot set parent to self!");
        }
        mParent = parent;
        // This tab may have been freed due to low memory. If that is the case,
        // the parent tab id is already saved. If we are changing that id
        // (most likely due to removing the parent tab) we must update the
        // parent tab id in the saved Bundle.
        if (mSavedState != null) {
            if (parent == null) {
                mSavedState.remove(PARENTTAB);
            } else {
                mSavedState.putLong(PARENTTAB, parent.getId());
            }
        }

        // Sync the WebView useragent with the parent
        if (parent != null && mSettings.hasDesktopUseragent(parent.getWebView())
                != mSettings.hasDesktopUseragent(getWebView())) {
            mSettings.toggleDesktopUseragent(getWebView());
        }

        if (parent != null && parent.getId() == getId()) {
            throw new IllegalStateException("Parent has same ID as child!");
        }
    }

    /**
     * If this Tab was created through another Tab, then this method returns
     * that Tab.
     * @return the Tab parent or null
     */
    public Tab getParent() {
        return mParent;
    }

    /**
     * When a Tab is created through the content of another Tab, then we
     * associate the Tabs.
     * @param child the Tab that was created from this Tab
     */
    void addChildTab(Tab child) {
        if (mChildren == null) {
            mChildren = new Vector<Tab>();
        }
        mChildren.add(child);
        child.setParent(this);
    }

    Vector<Tab> getChildren() {
        return mChildren;
    }

    void resume() {
        if (mMainView != null) {
            setupHwAcceleration(mMainView);
            mMainView.onResume();
            if (mSubView != null) {
                mSubView.onResume();
            }
        }
    }

    private void setupHwAcceleration(View web) {
        if (web == null) return;
        BrowserSettings settings = BrowserSettings.getInstance();
        if (settings.isHardwareAccelerated()) {
            web.setLayerType(View.LAYER_TYPE_NONE, null);
        } else {
            web.setLayerType(View.LAYER_TYPE_SOFTWARE, null);
        }
    }

    void pause() {
        if (mMainView != null) {
            mMainView.onPause();
            if (mSubView != null) {
                mSubView.onPause();
            }
        }
    }

    void putInForeground() {
        if (mInForeground) {
            return;
        }
        mInForeground = true;
        resume();
        Activity activity = mWebViewController.getActivity();
        mMainView.setOnCreateContextMenuListener(activity);
        if (mSubView != null) {
            mSubView.setOnCreateContextMenuListener(activity);
        }
        // Show the pending error dialog if the queue is not empty
        if (mQueuedErrors != null && mQueuedErrors.size() >  0) {
            showError(mQueuedErrors.getFirst());
        }
        mWebViewController.bookmarkedStatusHasChanged(this);
    }

    void putInBackground() {
        if (!mInForeground) {
            return;
        }
        capture();
        mInForeground = false;
        pause();
        mMainView.setOnCreateContextMenuListener(null);
        if (mSubView != null) {
            mSubView.setOnCreateContextMenuListener(null);
        }
    }

    boolean inForeground() {
        return mInForeground;
    }

    /**
     * Return the top window of this tab; either the subwindow if it is not
     * null or the main window.
     * @return The top window of this tab.
     */
    WebView getTopWindow() {
        if (mSubView != null) {
            return mSubView;
        }
        return mMainView;
    }

    /**
     * Return the main window of this tab. Note: if a tab is freed in the
     * background, this can return null. It is only guaranteed to be
     * non-null for the current tab.
     * @return The main WebView of this tab.
     */
    WebView getWebView() {
        /* Ensure the root webview object is in sync with our internal incognito status */
        if (mMainView instanceof BrowserWebView) {
            if (isPrivateBrowsingEnabled() && !mMainView.isPrivateBrowsingEnabled()) {
                ((BrowserWebView)mMainView).setPrivateBrowsing(isPrivateBrowsingEnabled());
            }
        }
        return mMainView;
    }

    void setViewContainer(View container) {
        mContainer = container;
    }

    View getViewContainer() {
        return mContainer;
    }

    /**
     * Return whether private browsing is enabled for the main window of
     * this tab.
     * @return True if private browsing is enabled.
     */
    boolean isPrivateBrowsingEnabled() {
        return mCurrentState.mIncognito;
    }

    /**
     * Return the subwindow of this tab or null if there is no subwindow.
     * @return The subwindow of this tab or null.
     */
    WebView getSubWebView() {
        return mSubView;
    }

    void setSubWebView(WebView subView) {
        mSubView = subView;
    }

    View getSubViewContainer() {
        return mSubViewContainer;
    }

    void setSubViewContainer(View subViewContainer) {
        mSubViewContainer = subViewContainer;
    }

    /**
     * @return The geolocation permissions prompt for this tab.
     */
    GeolocationPermissionsPrompt getGeolocationPermissionsPrompt() {
        if (mGeolocationPermissionsPrompt == null) {
            ViewStub stub = (ViewStub) mContainer
                    .findViewById(R.id.geolocation_permissions_prompt);
            mGeolocationPermissionsPrompt = (GeolocationPermissionsPrompt) stub
                    .inflate();
        }
        return mGeolocationPermissionsPrompt;
    }

    /**
     * @return The permissions prompt for this tab.
     */
    PermissionsPrompt getPermissionsPrompt() {
        if (mPermissionsPrompt == null) {
            ViewStub stub = (ViewStub) mContainer
                    .findViewById(R.id.permissions_prompt);
            mPermissionsPrompt = (PermissionsPrompt) stub.inflate();
        }
        return mPermissionsPrompt;
    }

    /**
     * @return The application id string
     */
    String getAppId() {
        return mAppId;
    }

    /**
     * Set the application id string
     * @param id
     */
    void setAppId(String id) {
        mAppId = id;
    }

    boolean closeOnBack() {
        return mCloseOnBack;
    }

    void setCloseOnBack(boolean close) {
        mCloseOnBack = close;
    }

    String getUrl() {
        return UrlUtils.filteredUrl(mCurrentState.mUrl);
    }

    String getOriginalUrl() {
        if (mCurrentState.mOriginalUrl == null) {
            return getUrl();
        }
        return UrlUtils.filteredUrl(mCurrentState.mOriginalUrl);
    }

    /**
     * Get the title of this tab.
     */
    String getTitle() {
        if (mCurrentState.mTitle == null && mInPageLoad) {
            return mContext.getString(R.string.title_bar_loading);
        }
        return mCurrentState.mTitle;
    }

    /**
     * Get the favicon of this tab.
     */
    Bitmap getFavicon() {
        if (mCurrentState.mFavicon != null) {
            return mCurrentState.mFavicon;
        }
        return getDefaultFavicon(mContext);
    }

    public boolean isBookmarkedSite() {
        return mCurrentState.mIsBookmarkedSite;
    }

    /**
     * Return the tab's error console. Creates the console if createIfNEcessary
     * is true and we haven't already created the console.
     * @param createIfNecessary Flag to indicate if the console should be
     *            created if it has not been already.
     * @return The tab's error console, or null if one has not been created and
     *         createIfNecessary is false.
     */
    ErrorConsoleView getErrorConsole(boolean createIfNecessary) {
        if (createIfNecessary && mErrorConsole == null) {
            mErrorConsole = new ErrorConsoleView(mContext);
            mErrorConsole.setWebView(mMainView);
        }
        return mErrorConsole;
    }

    /**
     * Sets the security state, clears the SSL certificate error and informs
     * the controller.
     */
    private void setSecurityState(SecurityState securityState) {
        mCurrentState.mSecurityState = securityState;
        mCurrentState.mSslCertificateError = null;
        mWebViewController.onUpdatedSecurityState(this);
    }

    /**
     * @return The tab's security state.
     */
    SecurityState getSecurityState() {
        return mCurrentState.mSecurityState;
    }

    /**
     * Gets the SSL certificate error, if any, for the page's main resource.
     * This is only non-null when the security state is
     * SECURITY_STATE_BAD_CERTIFICATE.
     */
    SslError getSslCertificateError() {
        return mCurrentState.mSslCertificateError;
    }

    int getLoadProgress() {
        if (mInPageLoad) {
            return mPageLoadProgress;
        }
        return 100;
    }

    /**
     * @return TRUE if onPageStarted is called while onPageFinished is not
     *         called yet.
     */
    boolean inPageLoad() {
        return mInPageLoad;
    }

    /**
     * @return The Bundle with the tab's state if it can be saved, otherwise null
     */
    public Bundle saveState() {
        // If the WebView is null it means we ran low on memory and we already
        // stored the saved state in mSavedState.
        if (mMainView == null) {
            return mSavedState;
        }

        if (TextUtils.isEmpty(mCurrentState.mUrl)) {
            return null;
        }

        mSavedState = new Bundle();
        WebBackForwardList savedList = mMainView.saveState(mSavedState);
        if (savedList == null || savedList.getSize() == 0) {
            Log.w(LOGTAG, "Failed to save back/forward list for "
                    + mCurrentState.mUrl);
        }

        mSavedState.putLong(ID, mId);
        mSavedState.putString(CURRURL, mCurrentState.mUrl);
        mSavedState.putString(CURRTITLE, mCurrentState.mTitle);
        mSavedState.putBoolean(INCOGNITO, mMainView.isPrivateBrowsingEnabled());
        if (mAppId != null) {
            mSavedState.putString(APPID, mAppId);
        }
        mSavedState.putBoolean(CLOSEFLAG, mCloseOnBack);
        // Remember the parent tab so the relationship can be restored.
        if (mParent != null) {
            mSavedState.putLong(PARENTTAB, mParent.mId);
        }
        mSavedState.putBoolean(USERAGENT,
                mSettings.hasDesktopUseragent(getWebView()));
        return mSavedState;
    }

    /*
     * Restore the state of the tab.
     */
    private void restoreState(Bundle b) {
        mSavedState = b;
        if (mSavedState == null) {
            return;
        }
        // Restore the internal state even if the WebView fails to restore.
        // This will maintain the app id, original url and close-on-exit values.
        mId = b.getLong(ID);
        mAppId = b.getString(APPID);
        mCloseOnBack = b.getBoolean(CLOSEFLAG);
        restoreUserAgent();
        String url = b.getString(CURRURL);
        String title = b.getString(CURRTITLE);
        boolean incognito = b.getBoolean(INCOGNITO);
        mCurrentState = new PageState(mContext, incognito, url, null);
        mCurrentState.mTitle = title;
        synchronized (Tab.this) {
            if (mCapture != null) {
                DataController.getInstance(mContext).loadThumbnail(this);
            }
        }
    }

    private void restoreUserAgent() {
        if (mMainView == null || mSavedState == null) {
            return;
        }
        if (mSavedState.getBoolean(USERAGENT)
                != mSettings.hasDesktopUseragent(mMainView)) {
            mSettings.toggleDesktopUseragent(mMainView);
        }
    }

    public void updateBookmarkedStatus() {
        mDataController.queryBookmarkStatus(getUrl(), mIsBookmarkCallback);
    }

    private DataController.OnQueryUrlIsBookmark mIsBookmarkCallback
            = new DataController.OnQueryUrlIsBookmark() {
        @Override
        public void onQueryUrlIsBookmark(String url, boolean isBookmark) {
            if (mCurrentState.mUrl.equals(url)) {
                mCurrentState.mIsBookmarkedSite = isBookmark;
                mWebViewController.bookmarkedStatusHasChanged(Tab.this);
            }
        }
    };

    public Bitmap getScreenshot() {
        synchronized (Tab.this) {
            return mCapture;
        }
    }

    public boolean isSnapshot() {
        return false;
    }

    private static class SaveCallback implements ValueCallback<Boolean> {
        boolean mResult;

        @Override
        public void onReceiveValue(Boolean value) {
            mResult = value;
            synchronized (this) {
                notifyAll();
            }
        }

    }

    /**
     * Must be called on the UI thread
     */
    public ContentValues createSnapshotValues() {
        return null;
    }

    /**
     * Probably want to call this on a background thread
     */
    public boolean saveViewState(ContentValues values) {
        return false;
    }

    public byte[] compressBitmap(Bitmap bitmap) {
        if (bitmap == null) {
            return null;
        }
        ByteArrayOutputStream stream = new ByteArrayOutputStream();
        bitmap.compress(CompressFormat.PNG, 100, stream);
        return stream.toByteArray();
    }

    public void loadUrl(String url, Map<String, String> headers) {
        if (mMainView != null) {
            mPageLoadProgress = INITIAL_PROGRESS;
            mInPageLoad = true;
            mCurrentState = new PageState(mContext, false, url, null);
            mWebViewController.onPageStarted(this, mMainView, null);
            WebResourceResponse res = HomeProvider.shouldInterceptRequest(mContext, url);
            if (res != null) {
                try {
                    String data = readWebResource(res).toString();
                    mInMostVisitedPage = true;
                    mMainView.loadDataWithBaseURL(url, data, res.getMimeType(), res.getEncoding(),
                            HomeProvider.MOST_VISITED_URL);
                } catch (IOException io) {
                    // Fallback to default load handling
                    mMainView.loadUrl(url, headers);
                }
            } else {
                mMainView.loadUrl(url, headers);
            }
        }
    }

    public void disableUrlOverridingForLoad() {
        mDisableOverrideUrlLoading = true;
    }

    protected void capture() {
        if (mMainView == null || mCapture == null) return;
        if (mMainView.getContentWidth() <= 0 || mMainView.getContentHeight() <= 0) {
            return;
        }
        Canvas c = new Canvas(mCapture);
        final int left = mMainView.getScrollX();
        final int top = mMainView.getScrollY() + mMainView.getVisibleTitleHeight();
        int state = c.save();
        c.translate(-left, -top);
        float scale = mCaptureWidth / (float) mMainView.getWidth();
        c.scale(scale, scale, left, top);
        if (mMainView instanceof BrowserWebView) {
            ((BrowserWebView)mMainView).drawContent(c);
        } else {
            mMainView.draw(c);
        }
        c.restoreToCount(state);
        // manually anti-alias the edges for the tilt
        c.drawRect(0, 0, 1, mCapture.getHeight(), sAlphaPaint);
        c.drawRect(mCapture.getWidth() - 1, 0, mCapture.getWidth(),
                mCapture.getHeight(), sAlphaPaint);
        c.drawRect(0, 0, mCapture.getWidth(), 1, sAlphaPaint);
        c.drawRect(0, mCapture.getHeight() - 1, mCapture.getWidth(),
                mCapture.getHeight(), sAlphaPaint);
        c.setBitmap(null);
        mHandler.removeMessages(MSG_CAPTURE);
        persistThumbnail();
        TabControl tc = mWebViewController.getTabControl();
        if (tc != null) {
            OnThumbnailUpdatedListener updateListener
                    = tc.getOnThumbnailUpdatedListener();
            if (updateListener != null) {
                updateListener.onThumbnailUpdated(this);
            }
        }
    }

    @Override
    public void onNewPicture(WebView view, Picture picture) {
        postCapture();
    }

    private void postCapture() {
        if (!mHandler.hasMessages(MSG_CAPTURE)) {
            mHandler.sendEmptyMessageDelayed(MSG_CAPTURE, CAPTURE_DELAY);
        }
    }

    public boolean canGoBack() {
        return mMainView != null ? mMainView.canGoBack() : false;
    }

    public boolean canGoForward() {
        return mMainView != null ? mMainView.canGoForward() : false;
    }

    public void goBack() {
        if (mMainView != null) {
            mMainView.goBack();
        }
    }

    public void goForward() {
        if (mMainView != null) {
            mMainView.goForward();
        }
    }

    /**
     * Causes the tab back/forward stack to be cleared once, if the given URL is the next URL
     * to be added to the stack.
     *
     * This is used to ensure that preloaded URLs that are not subsequently seen by the user do
     * not appear in the back stack.
     */
    public void clearBackStackWhenItemAdded(Pattern urlPattern) {
        mClearHistoryUrlPattern = urlPattern;
    }

    protected void persistThumbnail() {
        DataController.getInstance(mContext).saveThumbnail(this);
    }

    protected void deleteThumbnail() {
        DataController.getInstance(mContext).deleteThumbnail(this);
    }

    void updateCaptureFromBlob(byte[] blob) {
        synchronized (Tab.this) {
            if (mCapture == null) {
                return;
            }
            ByteBuffer buffer = ByteBuffer.wrap(blob);
            try {
                mCapture.copyPixelsFromBuffer(buffer);
            } catch (RuntimeException rex) {
                Log.e(LOGTAG, "Load capture has mismatched sizes; buffer: "
                        + buffer.capacity() + " blob: " + blob.length
                        + "capture: " + mCapture.getByteCount());
                throw rex;
            }
        }
    }

    @Override
    public String toString() {
        StringBuilder builder = new StringBuilder(100);
        builder.append(mId);
        builder.append(") has parent: ");
        if (getParent() != null) {
            builder.append("true[");
            builder.append(getParent().getId());
            builder.append("]");
        } else {
            builder.append("false");
        }
        builder.append(", incog: ");
        builder.append(isPrivateBrowsingEnabled());
        if (!isPrivateBrowsingEnabled()) {
            builder.append(", title: ");
            builder.append(getTitle());
            builder.append(", url: ");
            builder.append(getUrl());
        }
        return builder.toString();
    }

    private void handleProceededAfterSslError(SslError error) {
        if (error.getUrl().equals(mCurrentState.mUrl)) {
            // The security state should currently be SECURITY_STATE_SECURE.
            setSecurityState(SecurityState.SECURITY_STATE_BAD_CERTIFICATE);
            mCurrentState.mSslCertificateError = error;
        } else if (getSecurityState() == SecurityState.SECURITY_STATE_SECURE) {
            // The page's main resource is secure and this error is for a
            // sub-resource.
            setSecurityState(SecurityState.SECURITY_STATE_MIXED);
        }
    }

    public void setAcceptThirdPartyCookies(boolean accept) {
        CookieManager cookieManager = CookieManager.getInstance();
        if (mMainView != null)
            cookieManager.setAcceptThirdPartyCookies(mMainView, accept);
        if (mSubView != null)
            cookieManager.setAcceptThirdPartyCookies(mSubView, accept);
    }

    private StringBuilder readWebResource(WebResourceResponse response) throws IOException {
        StringBuilder sb = new StringBuilder();
        InputStream is = response.getData();
        try {
            byte[] data = new byte[512];
            int read = 0;
            while ((read = is.read(data, 0, 512)) != -1) {
                sb.append(new String(data, 0, read));
            }
        } finally {
            is.close();
        }
        return sb;
    }
}
